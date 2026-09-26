#include "share/atspre_staload.hats"
#use array as A
#use dict as D
#use result as R

(* A 4-slot table: fill it, overflow it, overwrite, remove, reuse the
   freed slot, and look everything up. Keys 1, 5, 9 all hash to slot 1
   (mod 4), so they exercise probing. Exits 1 on any mismatch. *)
typedef key = [i:int] int i

implement $D.hash_key<key> (k) = k
implement $D.equal_key<key> (a, b) = a = b

fn check (name: string, ok: bool): bool = let
  val () = (if ok then () else println! ("FAIL ", name))
in ok end

fn get (fd: !$D.frozen_dict(key, int), k: key): int =
  case+ $D.lookup<key><int>(fd, k) of
  | ~$R.some(x) => x
  | ~$R.none() => ~1

implement main0 () = let
  val d = $D.create<key><int>(4)
  val r1 = check("insert 1", $D.insert<key><int>(d, 1, 10))
  val r2 = check("insert 5 (collides)", $D.insert<key><int>(d, 5, 50))
  val r3 = check("insert 9 (collides)", $D.insert<key><int>(d, 9, 90))
  val r4 = check("insert 2", $D.insert<key><int>(d, 2, 20))
  val r5 = check("size 4", $D.size<key><int>(d) = 4)
  val r6 = check("insert into full table fails", ~($D.insert<key><int>(d, 3, 30)))
  val r7 = check("overwrite existing in full table", $D.insert<key><int>(d, 5, 55))
  val r8 = check("remove 5", $D.remove<key><int>(d, 5))
  val r9 = check("remove 5 again fails", ~($D.remove<key><int>(d, 5)))
  val r10 = check("size 3", $D.size<key><int>(d) = 3)
  val r11 = check("insert 3 reuses freed slot", $D.insert<key><int>(d, 3, 30))
  val fd = $D.dict_freeze<key><int>(d)
  val r12 = check("lookup 1", get(fd, 1) = 10)
  val r13 = check("lookup 9 (past removed slot)", get(fd, 9) = 90)
  val r14 = check("lookup 2", get(fd, 2) = 20)
  val r15 = check("lookup 3", get(fd, 3) = 30)
  val r16 = check("lookup 5 (removed)", get(fd, 5) = ~1)
  val r17 = check("lookup 7 (never inserted)", get(fd, 7) = ~1)
  val r18 = check("lookup -4 (negative key)", get(fd, ~4) = ~1)
  val d = $D.dict_thaw<key><int>(fd)
  val () = $D.dict_free<key><int>(d)
in
  if r1 && r2 && r3 && r4 && r5 && r6 && r7 && r8 && r9 && r10 && r11
     && r12 && r13 && r14 && r15 && r16 && r17 && r18
  then println! ("dict_ops: all cases pass")
  else exit_void(1)
end
