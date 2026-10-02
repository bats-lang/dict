#include "share/atspre_staload.hats"
#use array as A
#use dict as D
#use result as R

(* Keys are indexed ints, so the hash is an indexed int as the API
   requires; no cast anywhere. *)
typedef key = [i:int] int i

implement $D.hash_key<key> (k) = k
implement $D.equal_key<key> (a, b) = a = b

(* Whether 100, stored under 42, is found there *)
#pub fn roundtrip (): bool

implement roundtrip () = let
  val d = $D.create<key><int>(8)
  val ok = $D.insert<key><int>(d, 42, 100)
  val fd = $D.dict_freeze<key><int>(d)
  val found = (case+ $D.lookup<key><int>(fd, 42) of
    | ~$R.some(x) => x = 100 | ~$R.none() => false): bool
  val d = $D.dict_thaw<key><int>(fd)
  val () = $D.dict_free<key><int>(d)
in ok && found end
