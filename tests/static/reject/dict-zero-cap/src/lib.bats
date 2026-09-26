#use dict as D

typedef key = [i:int] int i

implement $D.hash_key<key> (k) = k
implement $D.equal_key<key> (a, b) = a = b

(* A zero-capacity table has no slots: must not type-check. *)
#pub fn zero (): void

implement zero () = let
  val d = $D.create<key><int>(0)
in $D.dict_free<key><int>(d) end
