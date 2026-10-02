#include "share/atspre_staload.hats"
#use array as A
#use dict as D

(* A slot's state is a choice, not the byte it is stored as *)
fn mark_used {ls:agz} (states: !$A.arr(byte, ls, 4)): void = $D._state_set(states, 0, 1)
