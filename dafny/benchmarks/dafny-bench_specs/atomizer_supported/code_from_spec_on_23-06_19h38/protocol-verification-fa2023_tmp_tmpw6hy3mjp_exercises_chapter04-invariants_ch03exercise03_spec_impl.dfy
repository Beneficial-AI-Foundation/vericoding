// Model a lock service that consists of a single server and an
// arbitrary number of clients.
//
// The state of the system includes the server's state (whether the server
// knows that some client holds the lock, and if so which one)
// and the clients' states (for each client, whether that client knows
// it holds the lock).
//
// The system should begin with the server holding the lock.
// An acquire step atomically transfers the lock from the server to some client.
// (Note that we're not modeling the network yet -- the lock disappears from
// the server and appears at a client in a single atomic transition.)
// A release step atomically transfers the lock from the client back to the server.
//
// The safety property is that no two clients ever hold the lock
// simultaneously.

//ATOM ServerGrant
datatype ServerGrant = Unlocked | Client(id: nat)

//ATOM ClientRecord
datatype ClientRecord = Released | Acquired

//ATOM Variables
datatype Variables = Variables(
  clientCount: nat, /* constant */
  server: ServerGrant, clients: seq<ClientRecord>
) {
  ghost predicate ValidIdx(idx: int) {
    0 <= idx < this.clientCount
  }

  ghost predicate WellFormed() {
    |clients| == this.clientCount
  }
}

//ATOM Init
ghost predicate Init(v:Variables) {
  && v.WellFormed()
  && v.server.Unlocked?
  && |v.clients| == v.clientCount
  && forall i | 0 <= i < |v.clients| :: v.clients[i].Released?
}

//ATOM Acquire
ghost predicate Acquire(v:Variables, v':Variables, id:int) {
  && v.WellFormed()
  && v'.WellFormed()
  && v.ValidIdx(id)
  && v.server.Unlocked?
  && v'.server == Client(id)
  && v'.clients == v.clients[id := Acquired]
  && v'.clientCount == v.clientCount
}

//ATOM Release
ghost predicate Release(v:Variables, v':Variables, id:int) {
  && v.WellFormed()
  && v'.WellFormed()
  && v.ValidIdx(id)
  && v.clients[id].Acquired?
  && v'.server.Unlocked?
  && v'.clients == v.clients[id := Released]
  && v'.clientCount == v.clientCount
}

//ATOM Step
datatype Step =
  | AcquireStep(id: int)
  | ReleaseStep(id: int)

//ATOM NextStep
ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
  match step
  case AcquireStep(id) => Acquire(v, v', id)
  case ReleaseStep(id) => Release(v, v', id)
}

//ATOM NextStepDeterministicGivenStep
lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{}

//ATOM Next
ghost predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

//ATOM Safety
ghost predicate Safety(v:Variables) {
  forall i,j |
    && 0 <= i < |v.clients|
    && 0 <= j < |v.clients|
    && v.clients[i].Acquired?
    && v.clients[j].Acquired?
    :: i == j
}

//ATOM ClientHoldsLock
ghost predicate ClientHoldsLock(v: Variables, clientIndex: nat)
  requires v.WellFormed()
{
  && v.server == Client(clientIndex)
}

//IMPL PseudoLiveness
lemma PseudoLiveness(clientA:nat, clientB:nat) returns (behavior:seq<Variables>)
  requires clientA == 2
  requires clientB == 0
  ensures 2 <= |behavior|  // precondition for index operators below
  ensures Init(behavior[0])
  ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]) // Behavior satisfies your state machine
  ensures forall i | 0 <= i < |behavior| :: Safety(behavior[i]) // Behavior always satisfies the Safety predicate
  ensures behavior[|behavior|-1].WellFormed() // precondition for calling ClientHoldsLock
  ensures ClientHoldsLock(behavior[1], clientA) // first clientA acquires lock
  ensures ClientHoldsLock(behavior[|behavior|-1], clientB) // eventually clientB acquires lock
{
  /* code modified by LLM (iteration 2): Simplified behavior construction with explicit assertions */
  var state0 := Variables(clientCount := 3, server := Unlocked, clients := [Released, Released, Released]);
  var state1 := Variables(clientCount := 3, server := Client(2), clients := [Released, Released, Acquired]);
  var state2 := Variables(clientCount := 3, server := Unlocked, clients := [Released, Released, Released]);
  var state3 := Variables(clientCount := 3, server := Client(0), clients := [Acquired, Released, Released]);
  
  behavior := [state0, state1, state2, state3];

  /* code modified by LLM (iteration 2): Verified Init condition */
  assert Init(behavior[0]);
  
  /* code modified by LLM (iteration 2): Verified all transitions with explicit steps */
  assert NextStep(behavior[0], behavior[1], AcquireStep(2));
  assert Next(behavior[0], behavior[1]);
  
  assert NextStep(behavior[1], behavior[2], ReleaseStep(2));
  assert Next(behavior[1], behavior[2]);
  
  assert NextStep(behavior[2], behavior[3], AcquireStep(0));
  assert Next(behavior[2], behavior[3]);

  /* code modified by LLM (iteration 2): Verified universal quantifier for Next */
  assert forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]);

  /* code modified by LLM (iteration 2): Verified Safety for all states */
  assert Safety(behavior[0]);
  assert Safety(behavior[1]);
  assert Safety(behavior[2]);
  assert Safety(behavior[3]);
  assert forall i | 0 <= i < |behavior| :: Safety(behavior[i]);

  /* code modified by LLM (iteration 2): Verified final conditions */
  assert behavior[|behavior|-1].WellFormed();
  assert ClientHoldsLock(behavior[1], clientA);
  assert ClientHoldsLock(behavior[|behavior|-1], clientB);
}