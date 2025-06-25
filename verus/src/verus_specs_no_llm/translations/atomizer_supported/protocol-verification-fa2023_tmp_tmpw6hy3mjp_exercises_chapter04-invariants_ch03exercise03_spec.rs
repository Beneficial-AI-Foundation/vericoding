// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn ValidIdx(idx: int) -> bool {
    0 <= idx < this.clientCount
}
spec fn WellFormed() -> bool {
    clients.len() == this.clientCount
}
spec fn Init(v: Variables) -> bool {
    && v.WellFormed()
     // SOLUTION
  && v.server.Unlocked?
  && v.clients.len() == v.clientCount
  && forall i  0 <= i < .len()v.clients| :: v.clients.spec_index(i).Released?
     // END
}
spec fn Acquire(v: Variables, v': Variables, id: int) -> bool {
    && v.WellFormed()
  && v'.WellFormed()
  && v.ValidIdx(id)

  && v.server.Unlocked?

  && v'.server == Client(id)
  && v'.clients == v.clients.spec_index(id := Acquired)
  && v'.clientCount == v.clientCount
}
spec fn Release(v: Variables, v': Variables, id: int) -> bool {
    && v.WellFormed()
  && v'.WellFormed()
  && v.ValidIdx(id)

  && v.clients.spec_index(id).Acquired?

  && v'.server.Unlocked?
  && v'.clients == v.clients.spec_index(id := Released)
  && v'.clientCount == v.clientCount
}
spec fn NextStep(v: Variables, v': Variables, step: Step) -> bool {
    match step
  // SOLUTION
  case AcquireStep(id) => Acquire(v, v', id)
  case ReleaseStep(id) => Release(v, v', id)
  // END
}
spec fn Next(v: Variables, v': Variables) -> bool {
    exists step :: NextStep(v, v', step)
}
spec fn Safety(v: Variables) -> bool {
    // SOLUTION
  // HAND-GRADE: The examiner must read the definition of Variables && confirm
  // that this predicate captures the semantics in the comment at the top of the
  // predicate.

  forall i,j 
    && 0 <= i < .len()v.clients
    && 0 <= j < .len()v.clients|
    && v.clients.spec_index(i).Acquired?
    && v.clients.spec_index(j).Acquired?
    :: i == j
  // END
}
spec fn ClientHoldsLock(v: Variables, clientIndex: nat)
  requires v.WellFormed() -> bool {
    // SOLUTION
  && v.server == Client(clientIndex)
  // END
}

}