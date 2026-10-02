#include "share/atspre_staload.hats"
#use array as A
#use dict as D

(* A match on a slot's state that leaves a removed slot out *)
fn holds_entry (state: $D.slot_state): bool =
  case+ state of
  | $D.Empty() => false
  | $D.Used() => true
