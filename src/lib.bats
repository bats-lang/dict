(* dict -- linear hash map with open addressing *)
(* Built entirely on safe array ops. No $UNSAFE, no assume. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use result as R

(* ============================================================
   Types
   ============================================================ *)

#pub datavtype dict(k:t@ype, v:t@ype) =
  | {li:agz}{lk:agz}{lv:agz}{lh:agz}{n:pos | n <= 65536}
    dict_mk(k, v) of (
      $A.arr(int, li, n),
      $A.arr(k, lk, n),
      $A.arr(v, lv, n),
      $A.arr(int, lh, n),
      int,
      int n,
      (k) -<cloref1> int,
      (k, k) -<cloref1> bool
    )

(* Frozen dict: vals frozen at refcount exactly 1, holding one borrow *)
#pub datavtype frozen_dict(k:t@ype, v:t@ype) =
  | {li:agz}{lk:agz}{lv:agz}{lh:agz}{n:pos | n <= 65536}
    fdict_mk(k, v) of (
      $A.arr(int, li, n),
      $A.arr(k, lk, n),
      $A.frozen(v, lv, n, 1),
      $A.borrow(v, lv, n),
      $A.arr(int, lh, n),
      int,
      int n,
      (k) -<cloref1> int,
      (k, k) -<cloref1> bool
    )

(* ============================================================
   API
   ============================================================ *)

#pub fun{k:t@ype}{v:t@ype}
create
  {n:pos | n <= 65536}
  (cap: int n, hash_fn: (k) -<cloref1> int, eq_fn: (k, k) -<cloref1> bool)
  : dict(k, v)

#pub fun{k:t@ype}{v:t@ype}
dict_free(d: dict(k, v)): void

#pub fun{k:t@ype}{v:t@ype}
insert(d: !dict(k, v), key: k, value: v): void

#pub fun{k:t@ype}{v:t@ype}
remove(d: !dict(k, v), key: k): bool

#pub fn{k:t@ype}{v:t@ype}
size(d: !dict(k, v)): int

#pub fun{k:t@ype}{v:t@ype}
dict_freeze(d: dict(k, v)): frozen_dict(k, v)

#pub fun{k:t@ype}{v:t@ype}
dict_thaw(d: frozen_dict(k, v)): dict(k, v)

#pub fun{k:t@ype}{v:t@ype}
find(d: !frozen_dict(k, v), key: k): $R.option(int)

#pub fn{k:t@ype}{v:t@ype}
get_key(d: !frozen_dict(k, v), idx: int): k

#pub fn{k:t@ype}{v:t@ype}
get_val(d: !frozen_dict(k, v), idx: int): v

#pub fun hash_bytes
  {lb:agz}{n:pos}
  (b: !$A.borrow(byte, lb, n), len: int n): int

(* ============================================================
   Probe helpers
   ============================================================ *)

fun{k:t@ype}{v:t@ype} _probe
  {li:agz}{lk:agz}{lh:agz}{n:pos}{fuel:nat} .<fuel>.
  (indices: !$A.arr(int, li, n),
   keys: !$A.arr(k, lk, n),
   hashes: !$A.arr(int, lh, n),
   eq_fn: (k, k) -<cloref1> bool,
   key: k, h: int, n: int n,
   slot: int, fuel: int fuel): int =
  if fuel <= 0 then ~1
  else let val s = g1ofg0(slot) in
    if s < 0 then ~1
    else if s >= n then ~1
    else let val idx = $A.get<int>(indices, s) in
      if idx = ~1 then ~1
      else if idx = ~2 then let
        val next = (if s + 1 >= n then 0 else g0ofg1(s + 1)): int
      in _probe<k><v>(indices, keys, hashes, eq_fn, key, h, n, next, fuel - 1) end
      else let val idx1 = g1ofg0(idx) in
        if idx1 < 0 then ~1
        else if idx1 >= n then ~1
        else if $A.get<int>(hashes, idx1) = h then
          (if eq_fn($A.get<k>(keys, idx1), key) then idx
           else let
             val next = (if s + 1 >= n then 0 else g0ofg1(s + 1)): int
           in _probe<k><v>(indices, keys, hashes, eq_fn, key, h, n, next, fuel - 1) end)
        else let
          val next = (if s + 1 >= n then 0 else g0ofg1(s + 1)): int
        in _probe<k><v>(indices, keys, hashes, eq_fn, key, h, n, next, fuel - 1) end
      end
    end
  end

fun{k:t@ype} _find_slot
  {li:agz}{n:pos}{fuel:nat} .<fuel>.
  (indices: !$A.arr(int, li, n), n: int n,
   slot: int, fuel: int fuel): int =
  if fuel <= 0 then 0
  else let val s = g1ofg0(slot) in
    if s < 0 then 0
    else if s >= n then 0
    else let val idx = $A.get<int>(indices, s) in
      if idx = ~1 then slot
      else if idx = ~2 then slot
      else let
        val next = (if s + 1 >= n then 0 else g0ofg1(s + 1)): int
      in _find_slot<k>(indices, n, next, fuel - 1) end
    end
  end

fn _start_slot {n:pos} (h: int, n: int n): int = let
  val s = h mod n
in if s >= 0 then s else s + n end

(* ============================================================
   Implementations
   ============================================================ *)

implement{k}{v}
create{n}(cap, hash_fn, eq_fn) = let
  val indices = $A.alloc<int>(cap)
  val keys = $A.alloc<k>(cap)
  val vals = $A.alloc<v>(cap)
  val hashes = $A.alloc<int>(cap)
  fun init {li:agz}{m:pos}{i:nat | i <= m} .<m - i>.
    (arr: !$A.arr(int, li, m), i: int i, m: int m): void =
    if i >= m then ()
    else let val () = $A.set<int>(arr, i, ~1)
    in init(arr, i + 1, m) end
  val () = init(indices, 0, cap)
in dict_mk(indices, keys, vals, hashes, 0, cap, hash_fn, eq_fn) end

implement{k}{v}
dict_free(d) = let
  val+ ~dict_mk(indices, keys, vals, hashes, _, _, _, _) = d
in
  $A.free<int>(indices);
  $A.free<k>(keys);
  $A.free<v>(vals);
  $A.free<int>(hashes)
end

implement{k}{v}
size(d) = let
  val+ @dict_mk(_, _, _, _, count, _, _, _) = d
  val c = count
  prval () = fold@(d)
in c end

implement{k}{v}
insert(d, key, value) = let
  val+ @dict_mk(indices, keys, vals, hashes, count, cap, hash_fn, eq_fn) = d
  val h = hash_fn(key)
  val start = _start_slot(h, cap)
  val existing = _probe<k><v>(indices, keys, hashes, eq_fn, key, h, cap, start, cap)
in
  if existing >= 0 then let
    val ei = g1ofg0(existing)
  in
    if ei >= 0 then
      if ei < cap then let
        val () = $A.set<v>(vals, ei, value)
        prval () = fold@(d)
      in end
      else let prval () = fold@(d) in end
    else let prval () = fold@(d) in end
  end
  else let
    val slot = _find_slot<k>(indices, cap, start, cap)
    val s1 = g1ofg0(slot)
    val ei = g1ofg0(count)
  in
    if s1 >= 0 then
      if s1 < cap then
        if ei >= 0 then
          if ei < cap then let
            val () = $A.set<k>(keys, ei, key)
            val () = $A.set<v>(vals, ei, value)
            val () = $A.set<int>(hashes, ei, h)
            val () = $A.set<int>(indices, s1, count)
            val () = count := count + 1
            prval () = fold@(d)
          in end
          else let prval () = fold@(d) in end
        else let prval () = fold@(d) in end
      else let prval () = fold@(d) in end
    else let prval () = fold@(d) in end
  end
end

implement{k}{v}
remove(d, key) = let
  val+ @dict_mk(indices, keys, vals, hashes, count, cap, hash_fn, eq_fn) = d
  val h = hash_fn(key)
  val start = _start_slot(h, cap)
  fun find_rm
    {li:agz}{lk:agz}{lh:agz}{n:pos}{fuel:nat} .<fuel>.
    (indices: !$A.arr(int, li, n), keys: !$A.arr(k, lk, n),
     hashes: !$A.arr(int, lh, n), eq_fn: (k, k) -<cloref1> bool,
     key: k, h: int, n: int n, slot: int, fuel: int fuel): int =
    if fuel <= 0 then ~1
    else let val s = g1ofg0(slot) in
      if s < 0 then ~1
      else if s >= n then ~1
      else let val idx = $A.get<int>(indices, s) in
        if idx = ~1 then ~1
        else if idx = ~2 then let
          val next = (if s + 1 >= n then 0 else g0ofg1(s + 1)): int
        in find_rm(indices, keys, hashes, eq_fn, key, h, n, next, fuel - 1) end
        else let val idx1 = g1ofg0(idx) in
          if idx1 < 0 then ~1
          else if idx1 >= n then ~1
          else if $A.get<int>(hashes, idx1) = h then
            (if eq_fn($A.get<k>(keys, idx1), key) then slot
             else let
               val next = (if s + 1 >= n then 0 else g0ofg1(s + 1)): int
             in find_rm(indices, keys, hashes, eq_fn, key, h, n, next, fuel - 1) end)
          else let
            val next = (if s + 1 >= n then 0 else g0ofg1(s + 1)): int
          in find_rm(indices, keys, hashes, eq_fn, key, h, n, next, fuel - 1) end
        end
      end
    end
  val found = find_rm(indices, keys, hashes, eq_fn, key, h, cap, start, cap)
  val fs = g1ofg0(found)
in
  if fs >= 0 then
    if fs < cap then let
      val () = $A.set<int>(indices, fs, ~2)
      prval () = fold@(d)
    in true end
    else let prval () = fold@(d) in false end
  else let prval () = fold@(d) in false end
end

(* freeze: freeze vals, keep one borrow for reads *)
implement{k}{v}
dict_freeze(d) = let
  val+ ~dict_mk(indices, keys, vals, hashes, count, cap, hash_fn, eq_fn) = d
  val @(fz, bv) = $A.freeze<v>(vals)
in fdict_mk(indices, keys, fz, bv, hashes, count, cap, hash_fn, eq_fn) end

(* thaw: drop the stored borrow, thaw frozen vals back to mutable *)
implement{k}{v}
dict_thaw(d) = let
  val+ ~fdict_mk(indices, keys, fz, bv, hashes, count, cap, hash_fn, eq_fn) = d
  val () = $A.drop<v>(fz, bv)
  val vals = $A.thaw<v>(fz)
in dict_mk(indices, keys, vals, hashes, count, cap, hash_fn, eq_fn) end

(* find: probe using keys array (mutable, accessed via get) *)
implement{k}{v}
find(d, key) = let
  val+ @fdict_mk(indices, keys, _, _, hashes, _, cap, hash_fn, eq_fn) = d
  val h = hash_fn(key)
  val start = _start_slot(h, cap)
  val idx = _probe<k><v>(indices, keys, hashes, eq_fn, key, h, cap, start, cap)
  prval () = fold@(d)
in
  if idx >= 0 then $R.some(idx)
  else $R.none()
end

(* get_key: read from keys array (still mutable in frozen_dict) *)
implement{k}{v}
get_key(d, idx) = let
  val+ @fdict_mk(_, keys, _, _, _, _, cap, _, _) = d
  val idx1 = g1ofg0(idx)
  val k0 = (if idx1 >= 0 then
    (if idx1 < cap then $A.get<k>(keys, idx1) else $A.get<k>(keys, 0))
  else $A.get<k>(keys, 0)): k
  prval () = fold@(d)
in k0 end

(* get_val: read from frozen vals via stored borrow *)
implement{k}{v}
get_val(d, idx) = let
  val+ @fdict_mk(_, _, _, bv, _, _, cap, _, _) = d
  val idx1 = g1ofg0(idx)
  val v0 = (if idx1 >= 0 then
    (if idx1 < cap then $A.read<v>(bv, idx1) else $A.read<v>(bv, 0))
  else $A.read<v>(bv, 0)): v
  prval () = fold@(d)
in v0 end

(* ============================================================
   hash_bytes -- FNV-1a
   ============================================================ *)

implement hash_bytes{lb}{n}(b, len) = let
  fun loop {lb:agz}{n:pos}{i:nat | i <= n} .<n - i>.
    (b: !$A.borrow(byte, lb, n), i: int i, len: int n, h: int): int =
    if i >= len then h
    else let
      val bval = byte2int0($A.read<byte>(b, i))
      val h2 = ($AR.bor_int_int(h, bval) - $AR.band_int_int(h, bval)) * 16777619
    in loop(b, i + 1, len, h2) end
in loop(b, 0, len, 0) end

(* ============================================================
   Static tests
   ============================================================ *)

fn _test_create_free(): void = let
  val d = create<int><int>(16,
    lam (k: int): int =<cloref1> k,
    lam (a: int, b: int): bool =<cloref1> a = b)
  val () = dict_free<int><int>(d)
in () end

fn _test_insert_find(): void = let
  val d = create<int><int>(16,
    lam (k: int): int =<cloref1> k,
    lam (a: int, b: int): bool =<cloref1> a = b)
  val () = insert<int><int>(d, 42, 100)
  val () = insert<int><int>(d, 7, 200)
  val fd = dict_freeze<int><int>(d)
  val opt = find<int><int>(fd, 42)
  val () = case+ opt of
    | ~$R.some(idx) => let val v0 = get_val<int><int>(fd, idx) in () end
    | ~$R.none() => ()
  val d = dict_thaw<int><int>(fd)
  val () = dict_free<int><int>(d)
in () end

fn _test_remove(): void = let
  val d = create<int><int>(16,
    lam (k: int): int =<cloref1> k,
    lam (a: int, b: int): bool =<cloref1> a = b)
  val () = insert<int><int>(d, 10, 50)
  val removed = remove<int><int>(d, 10)
  val () = dict_free<int><int>(d)
in () end
