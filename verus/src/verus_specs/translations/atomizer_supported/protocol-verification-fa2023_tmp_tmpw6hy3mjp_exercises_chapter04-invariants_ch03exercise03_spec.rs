use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Specification)]
pub enum ServerGrant {
    Unlocked,
    Client { id: nat },
}

#[derive(PartialEq, Eq, Specification)]
pub enum ClientRecord {
    Released,
    Acquired,
}

#[derive(PartialEq, Eq, Specification)]
pub struct Variables {
    pub clientCount: nat,
    pub server: ServerGrant,
    pub clients: Seq<ClientRecord>,
}

impl Variables {
    pub open spec fn ValidIdx(self, idx: int) -> bool {
        0 <= idx < self.clientCount
    }

    pub open spec fn WellFormed(self) -> bool {
        self.clients.len() == self.clientCount
    }
}

pub open spec fn Init(v: Variables) -> bool {
    && v.WellFormed()
    && v.server == ServerGrant::Unlocked
    && v.clients.len() == v.clientCount
    && forall|i: int| 0 <= i < v.clients.len() ==> v.clients[i] == ClientRecord::Released
}

pub open spec fn Acquire(v: Variables, v_prime: Variables, id: int) -> bool {
    && v.WellFormed()
    && v_prime.WellFormed()
    && v.ValidIdx(id)
    && v.server == ServerGrant::Unlocked
    && v_prime.server == ServerGrant::Client { id: id as nat }
    && v_prime.clients == v.clients.update(id, ClientRecord::Acquired)
    && v_prime.clientCount == v.clientCount
}

pub open spec fn Release(v: Variables, v_prime: Variables, id: int) -> bool {
    && v.WellFormed()
    && v_prime.WellFormed()
    && v.ValidIdx(id)
    && v.clients[id] == ClientRecord::Acquired
    && v_prime.server == ServerGrant::Unlocked
    && v_prime.clients == v.clients.update(id, ClientRecord::Released)
    && v_prime.clientCount == v.clientCount
}

#[derive(PartialEq, Eq, Specification)]
pub enum Step {
    AcquireStep { id: int },
    ReleaseStep { id: int },
}

pub open spec fn NextStep(v: Variables, v_prime: Variables, step: Step) -> bool {
    match step {
        Step::AcquireStep { id } => Acquire(v, v_prime, id),
        Step::ReleaseStep { id } => Release(v, v_prime, id),
    }
}

pub proof fn NextStepDeterministicGivenStep(v: Variables, v_prime: Variables, step: Step)
    requires NextStep(v, v_prime, step)
    ensures forall|v_prime_prime: Variables| NextStep(v, v_prime_prime, step) ==> v_prime == v_prime_prime
{
}

pub open spec fn Next(v: Variables, v_prime: Variables) -> bool {
    exists|step: Step| NextStep(v, v_prime, step)
}

pub open spec fn Safety(v: Variables) -> bool {
    forall|i: int, j: int|
        0 <= i < v.clients.len()
        && 0 <= j < v.clients.len()
        && v.clients[i] == ClientRecord::Acquired
        && v.clients[j] == ClientRecord::Acquired
        ==> i == j
}

pub open spec fn ClientHoldsLock(v: Variables, clientIndex: nat) -> bool
    recommends v.WellFormed()
{
    v.server == ServerGrant::Client { id: clientIndex }
}

pub proof fn PseudoLiveness(clientA: nat, clientB: nat) -> (behavior: Seq<Variables>)
    requires clientA == 2
    requires clientB == 0
    ensures 2 <= behavior.len()
    ensures Init(behavior[0])
    ensures forall|i: int| 0 <= i < behavior.len() - 1 ==> Next(behavior[i], behavior[i + 1])
    ensures forall|i: int| 0 <= i < behavior.len() ==> Safety(behavior[i])
    ensures behavior[behavior.len() - 1].WellFormed()
    ensures ClientHoldsLock(behavior[1], clientA)
    ensures ClientHoldsLock(behavior[behavior.len() - 1], clientB)
{
}

}