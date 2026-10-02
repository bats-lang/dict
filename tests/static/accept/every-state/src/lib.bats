#include "share/atspre_staload.hats"
#use array as A
#use dict as D

(* Every slot state named, and one stored and read back *)
fn holds_entry (state: $D.slot_state): bool =
  case+ state of
  | $D.Empty() => false
  | $D.Used() => true
  | $D.Removed() => false

fn round_trip (): bool = let
  val states = $A.alloc<byte>(4)
  val () = $D._state_set(states, 2, $D.Used())
  val used = holds_entry($D._state_at(states, 2))
  val empty = ~holds_entry($D._state_at(states, 0))
  val () = $A.free<byte>(states)
in used && empty end
