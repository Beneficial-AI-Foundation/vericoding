// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Init(v: Variables) -> bool {
    && v.piles.len() == 3
  && v.turn.P1? // syntax
}
spec fn Turn(v: Variables, v': Variables, step: Step)
  requires step.TurnStep?
{
  var p := step.p;
  var take := step.take;
  && p < |v.piles|
  && take <= v.piles[p]
  && v' == v.(piles := v.piles[p := v.piles[p] - take]).(turn := v.turn.Other())
}


// nearly boilerplate (just gather up all transitions)
// ATOM 

// nearly boilerplate (just gather up all transitions)
ghost predicate NextStep(v: Variables, v': Variables, step: Step) -> bool {
    match step {
    case TurnStep(_, _) => Turn(v, v', step)
    case NoOpStep() => v' == v // we don't really need to define predicate NoOp
}
spec fn Next(v: Variables, v': Variables) -> bool {
    exists |step: int| NextStep(v, v', step)
}

spec fn Other() -> Player
{
    0
}

}