#use dict as D
#use result as R

(* Keys are indexed ints, so the hash is an indexed int as the API
   requires; no cast anywhere. *)
typedef key = [i:int] int i

implement $D.hash_key<key> (k) = k
implement $D.equal_key<key> (a, b) = a = b

#pub fn roundtrip (): int

implement roundtrip () = let
  val d = $D.create<key><int>(8)
  val ok = $D.insert<key><int>(d, 42, 100)
  val fd = $D.dict_freeze<key><int>(d)
  val v = (case+ $D.lookup<key><int>(fd, 42) of
    | ~$R.some(x) => x | ~$R.none() => ~1): int
  val d = $D.dict_thaw<key><int>(fd)
  val () = $D.dict_free<key><int>(d)
in if ok then v else ~1 end
