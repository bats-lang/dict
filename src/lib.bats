(* dict -- linear hash map with open addressing *)
(* Built entirely on safe array ops. No $UNSAFE, no assume, no casts:
   every index is proven by the types. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use result as R

(* ============================================================
   Types
   ============================================================ *)

(* Slot states. Keys, values and hashes live in the slot the probe
   chose, so no stored value is ever used as an index: every index is a
   probe position, proven < n by construction. *)
#define EMPTY 0
#define USED 1
#define REMOVED 2

(* c <= n live entries. *)
#pub datavtype dict(k:t@ype, v:t@ype) =
  | {ls:agz}{lk:agz}{lv:agz}{lh:agz}{n:pos | n <= 65536}{c:nat | c <= n}
    dict_mk(k, v) of (
      $A.arr(int, ls, n),
      $A.arr(k, lk, n),
      $A.arr(v, lv, n),
      $A.arr(int, lh, n),
      int c,
      int n
    )

(* Frozen dict: vals frozen at refcount exactly 1, holding one borrow *)
#pub datavtype frozen_dict(k:t@ype, v:t@ype) =
  | {ls:agz}{lk:agz}{lv:agz}{lh:agz}{n:pos | n <= 65536}{c:nat | c <= n}
    fdict_mk(k, v) of (
      $A.arr(int, ls, n),
      $A.arr(k, lk, n),
      $A.frozen(v, lv, n, 1),
      $A.borrow(v, lv, n),
      $A.arr(int, lh, n),
      int c,
      int n
    )

(* ============================================================
   API
   ============================================================ *)

(* Hashing and equality for a key type are supplied by the client as
   template implementations:
     implement $D.hash_key<key> (k) = ...
     implement $D.equal_key<key> (a, b) = ...
   The hash may be any int; it is folded into a slot without casts. *)
#pub fun{k:t@ype} hash_key (key: k): [h:int] int h

#pub fun{k:t@ype} equal_key (a: k, b: k): bool

#pub fun{k:t@ype}{v:t@ype}
create
  {n:pos | n <= 65536}
  (cap: int n)
  : dict(k, v)

#pub fun{k:t@ype}{v:t@ype}
dict_free(d: dict(k, v)): void

(* Insert or overwrite. Returns false, changing nothing, when the key is
   new and the table has no room left. *)
#pub fun{k:t@ype}{v:t@ype}
insert(d: !dict(k, v), key: k, value: v): bool

#pub fun{k:t@ype}{v:t@ype}
remove(d: !dict(k, v), key: k): bool

#pub fn{k:t@ype}{v:t@ype}
size(d: !dict(k, v)): int

#pub fun{k:t@ype}{v:t@ype}
dict_freeze(d: dict(k, v)): frozen_dict(k, v)

#pub fun{k:t@ype}{v:t@ype}
dict_thaw(d: frozen_dict(k, v)): dict(k, v)

(* The value stored for key, if any. *)
#pub fun{k:t@ype}{v:t@ype}
lookup(d: !frozen_dict(k, v), key: k): $R.option(v)

#pub fun hash_bytes
  {lb:agz}{n:pos}
  (b: !$A.borrow(byte, lb, n), len: int n): [h:nat] int h

(* ============================================================
   Probe helpers
   ============================================================ *)

(* Helpers below are public because the templates above call them, and
   templates are instantiated in the client's compilation unit. *)

(* Next slot, wrapping around. *)
#pub fn _next {n:pos}{s:nat | s < n} (s: int s, n: int n): [t:nat | t < n] int t

implement _next (s, n) = if s + 1 < n then s + 1 else 0

(* Start slot for a hash: fold any int into [0, n) without overflow. *)
#pub fn _start_slot {n:pos}{h:int} (h: int h, n: int n): [s:nat | s < n] int s

implement _start_slot (h, n) = if h >= 0 then nmod(h, n) else nmod(~(h + 1), n)

(* The slot holding key, or ~1. Visits each slot at most once: the
   step count f bounds the search; an EMPTY slot ends it. *)
fun{k:t@ype} _probe
  {ls:agz}{lk:agz}{lh:agz}{n:pos}{s:nat | s < n}{f:nat} .<f>.
  (states: !$A.arr(int, ls, n),
   keys: !$A.arr(k, lk, n),
   hashes: !$A.arr(int, lh, n),
   key: k, h: int, n: int n,
   s: int s, f: int f): [r:int | ~1 <= r; r < n] int r =
  if f <= 0 then ~1
  else let
    val st = $A.get<int>(states, s)
  in
    if st = EMPTY then ~1
    else if st = USED then
      (if $A.get<int>(hashes, s) = h then
         (if equal_key<k>($A.get<k>(keys, s), key) then s
          else _probe<k>(states, keys, hashes, key, h, n, _next(s, n), f - 1))
       else _probe<k>(states, keys, hashes, key, h, n, _next(s, n), f - 1))
    else _probe<k>(states, keys, hashes, key, h, n, _next(s, n), f - 1)
  end

(* First EMPTY or REMOVED slot from s, or ~1 if every slot is used. *)
#pub fn _free_slot
  {ls:agz}{n:pos}{s:nat | s < n}
  (states: !$A.arr(int, ls, n), n: int n, s: int s)
  : [r:int | ~1 <= r; r < n] int r

implement _free_slot {ls}{n}{s} (states, n, s) = let
  fun loop {t:nat | t < n}{f:nat} .<f>.
    (states: !$A.arr(int, ls, n), n: int n, t: int t, f: int f)
    : [r:int | ~1 <= r; r < n] int r =
    if f <= 0 then ~1
    else if $A.get<int>(states, t) = USED then loop(states, n, _next(t, n), f - 1)
    else t
in loop(states, n, s, n) end

(* ============================================================
   Implementations
   ============================================================ *)

implement{k}{v}
create{n}(cap) = let
  val states = $A.alloc<int>(cap)
  val keys = $A.alloc<k>(cap)
  val vals = $A.alloc<v>(cap)
  val hashes = $A.alloc<int>(cap)
  fun init {ls:agz}{i:nat | i <= n} .<n - i>.
    (arr: !$A.arr(int, ls, n), i: int i, m: int n): void =
    if i >= m then ()
    else let val () = $A.set<int>(arr, i, EMPTY)
    in init(arr, i + 1, m) end
  val () = init(states, 0, cap)
in dict_mk(states, keys, vals, hashes, 0, cap) end

implement{k}{v}
dict_free(d) = let
  val+ ~dict_mk(states, keys, vals, hashes, _, _) = d
in
  $A.free<int>(states);
  $A.free<k>(keys);
  $A.free<v>(vals);
  $A.free<int>(hashes)
end

implement{k}{v}
size(d) = let
  val+ @dict_mk(_, _, _, _, count, _) = d
  val c = count
  prval () = fold@(d)
in c end

implement{k}{v}
insert(d, key, value) = let
  val+ @dict_mk(states, keys, vals, hashes, count, cap) = d
  val h = hash_key<k>(key)
  val start = _start_slot(h, cap)
  val existing = _probe<k>(states, keys, hashes, key, h, cap, start, cap)
in
  if existing >= 0 then let
    val () = $A.set<v>(vals, existing, value)
    prval () = fold@(d)
  in true end
  else if count >= cap then let
    prval () = fold@(d)
  in false end
  else let
    val slot = _free_slot(states, cap, start)
  in
    if slot < 0 then let
      prval () = fold@(d)
    in false end
    else let
      val () = $A.set<k>(keys, slot, key)
      val () = $A.set<v>(vals, slot, value)
      val () = $A.set<int>(hashes, slot, h)
      val () = $A.set<int>(states, slot, USED)
      val () = count := count + 1
      prval () = fold@(d)
    in true end
  end
end

implement{k}{v}
remove(d, key) = let
  val+ @dict_mk(states, keys, vals, hashes, count, cap) = d
  val h = hash_key<k>(key)
  val start = _start_slot(h, cap)
  val found = _probe<k>(states, keys, hashes, key, h, cap, start, cap)
in
  if found >= 0 then
    (if count > 0 then let
       val () = $A.set<int>(states, found, REMOVED)
       val () = count := count - 1
       prval () = fold@(d)
     in true end
     else let prval () = fold@(d) in false end)
  else let prval () = fold@(d) in false end
end

(* freeze: freeze vals, keep one borrow for reads *)
implement{k}{v}
dict_freeze(d) = let
  val+ ~dict_mk(states, keys, vals, hashes, count, cap) = d
  val @(fz, bv) = $A.freeze<v>(vals)
in fdict_mk(states, keys, fz, bv, hashes, count, cap) end

(* thaw: drop the stored borrow, thaw frozen vals back to mutable *)
implement{k}{v}
dict_thaw(d) = let
  val+ ~fdict_mk(states, keys, fz, bv, hashes, count, cap) = d
  val () = $A.drop<v>(fz, bv)
  val vals = $A.thaw<v>(fz)
in dict_mk(states, keys, vals, hashes, count, cap) end

implement{k}{v}
lookup(d, key) = let
  val+ @fdict_mk(states, keys, _, bv, hashes, _, cap) = d
  val h = hash_key<k>(key)
  val start = _start_slot(h, cap)
  val idx = _probe<k>(states, keys, hashes, key, h, cap, start, cap)
  val r = (if idx >= 0 then $R.some($A.read<v>(bv, idx)) else $R.none()): $R.option(v)
  prval () = fold@(d)
in r end

(* The value of a byte as an int proven in [0, 256), rebuilt from its
   bits: each term is a literal or 0, so no cast is needed. *)
fn _byte_val (b: byte): [v:nat | v < 256] int v = let
  val c = byte2int0(b)
  fn bit {w:nat | w < 256} (c: int, w: int w): [x:nat | x <= w] int x =
    if $AR.band_int_int(c, w) = 0 then 0 else w
in
  bit(c, 128) + bit(c, 64) + bit(c, 32) + bit(c, 16)
    + bit(c, 8) + bit(c, 4) + bit(c, 2) + bit(c, 1)
end

(* ============================================================
   hash_bytes -- polynomial hash reduced modulo a prime, so every
   intermediate value stays in range (no signed overflow).
   ============================================================ *)

implement hash_bytes{lb}{n}(b, len) = let
  fun loop {i:nat | i <= n}{h:nat | h < 1000003} .<n - i>.
    (b: !$A.borrow(byte, lb, n), i: int i, len: int n, h: int h): [r:nat] int r =
    if i >= len then h
    else let
      val c = _byte_val($A.read<byte>(b, i))
    in loop(b, i + 1, len, nmod(h * 31 + c, 1000003)) end
in loop(b, 0, len, 0) end
