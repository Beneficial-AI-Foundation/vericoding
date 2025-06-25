// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn ValidIdx(idx: int) -> bool {
    0 <= idx < this.clientCount
}

spec fn WellFormed() -> bool {
    clients.len() == this.clientCount
}

spec fn Init(v: Variables) -> bool {
    and v.WellFormed()
     // SOLUTION
  and v.server.Unlocked?
  and v.clients.len() == v.clientCount
  and forall|i  0 <= i < .len()v.clients|: int| v.clients[i].Released?
     // END
}

spec fn Acquire(v: Variables, v': Variables, id: int) -> bool {
    and v.WellFormed()
  and v'.WellFormed()
  and v.ValidIdx(id)

  and v.server.Unlocked?

  and v'.server == Client(id)
  and v'.clients == v.clients[id := Acquired]
  and v'.clientCount == v.clientCount
}

spec fn Release(v: Variables, v': Variables, id: int) -> bool {
    and v.WellFormed()
  and v'.WellFormed()
  and v.ValidIdx(id)

  and v.clients[id].Acquired?

  and v'.server.Unlocked?
  and v'.clients == v.clients[id := Released]
  and v'.clientCount == v.clientCount
}

spec fn NextStep(v: Variables, v': Variables, step: Step) -> bool {
    match step
  // SOLUTION
  case AcquireStep(id) => Acquire(v, v', id)
  case ReleaseStep(id) => Release(v, v', id)
  // END
}

spec fn Next(v: Variables, v': Variables) -> bool {
    exists|step: int| NextStep(v, v', step)
}

spec fn Safety(v: Variables) -> bool {
    // SOLUTION
  // HAND-GRADE: The examiner must read the definition of Variables and confirm
  // that this predicate captures the semantics in the comment at the top of the
  // predicate.

  forall|i: int, j 
    and 0 <= i < .len()v.clients
    and 0 <= j < .len()v.clients|
    and v.clients[i].Acquired?
    and v.clients[j].Acquired?: int| i == j
  // END
}

spec fn ClientHoldsLock(v: Variables, clientIndex: nat)
  requires v.WellFormed() -> bool {
    // SOLUTION
  and v.server == Client(clientIndex)
  // END
}

}