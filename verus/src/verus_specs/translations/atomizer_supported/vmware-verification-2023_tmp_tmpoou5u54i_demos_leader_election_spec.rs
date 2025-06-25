use vstd::prelude::*;

verus! {

// Each node's identifier (address)
// ATOM 
// Each node's identifier (address)
pub struct Constants {
    pub ids: Seq<nat>,
}

impl Constants {
    pub open spec fn ValidIdx(&self, i: int) -> bool {
        0 <= i < self.ids.len()
    }

    pub open spec fn UniqueIds(&self) -> bool {
        forall|i: int, j: int| self.ValidIdx(i) && self.ValidIdx(j) && self.ids[i] == self.ids[j] ==> i == j
    }

    pub open spec fn WF(&self) -> bool {
        &&& 0 < self.ids.len()
        &&& self.UniqueIds()
    }
}

// The highest other identifier this node has heard about.
// ATOM 

// The highest other identifier this node has heard about.
pub struct Variables {
    pub highest_heard: Seq<int>,
}

impl Variables {
    pub open spec fn WF(&self, c: Constants) -> bool {
        &&& c.WF()
        &&& self.highest_heard.len() == c.ids.len()
    }
}

// ATOM 

pub open spec fn Init(c: Constants, v: Variables) -> bool {
    &&& v.WF(c)
    &&& c.UniqueIds()
    // Everyone begins having heard about nobody, not even themselves.
    &&& forall|i: int| c.ValidIdx(i) ==> v.highest_heard[i] == -1
}

// ATOM 

pub open spec fn max(a: int, b: int) -> int {
    if a > b { a } else { b }
}

// ATOM 

pub open spec fn NextIdx(c: Constants, idx: nat) -> nat
    recommends c.WF(), c.ValidIdx(idx as int)
{
    if idx + 1 == c.ids.len() { 0 } else { idx + 1 }
}

// ATOM 

pub open spec fn Transmission(c: Constants, v: Variables, v_prime: Variables, srcidx: nat) -> bool {
    &&& v.WF(c)
    &&& v_prime.WF(c)
    &&& c.ValidIdx(srcidx as int)
    // Neighbor address in ring.
    &&& {
        let dstidx = NextIdx(c, srcidx);
        // srcidx sends the max of its highest_heard value and its own id.
        let message = max(v.highest_heard[srcidx as int], c.ids[srcidx as int]);
        // dstidx only overwrites its highest_heard if the message is higher.
        let dst_new_max = max(v.highest_heard[dstidx as int], message);
        // XXX Manos: How could this have been a bug!? How could a srcidx, having sent message X, ever send message Y < X!?
        v_prime == Variables { highest_heard: v.highest_heard.update(dstidx as int, dst_new_max) }
    }
}

// ATOM 

pub enum Step {
    TransmissionStep { srcidx: nat },
}

// ATOM 

pub open spec fn NextStep(c: Constants, v: Variables, v_prime: Variables, step: Step) -> bool {
    match step {
        Step::TransmissionStep { srcidx } => Transmission(c, v, v_prime, srcidx),
    }
}

// ATOM 

pub open spec fn Next(c: Constants, v: Variables, v_prime: Variables) -> bool {
    exists|step: Step| NextStep(c, v, v_prime, step)
}

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

// ATOM 

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

pub open spec fn IsLeader(c: Constants, v: Variables, i: int) -> bool
    recommends v.WF(c)
{
    &&& c.ValidIdx(i)
    &&& v.highest_heard[i] == c.ids[i]
}

// ATOM 

pub open spec fn Safety(c: Constants, v: Variables) -> bool
    recommends v.WF(c)
{
    forall|i: int, j: int| IsLeader(c, v, i) && IsLeader(c, v, j) ==> i == j
}

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

// ATOM 

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

pub open spec fn IsChord(c: Constants, v: Variables, start: int, end: int) -> bool {
    &&& v.WF(c)
    &&& c.ValidIdx(start)
    &&& c.ValidIdx(end)
    &&& c.ids[start] == v.highest_heard[end]
}

// ATOM 

pub open spec fn Between(start: int, node: int, end: int) -> bool {
    if start < end {
        start < node < end // not wrapped
    } else {
        node < end || start < node // wrapped
    }
}

// ATOM 

pub open spec fn OnChordHeardDominatesId(c: Constants, v: Variables, start: int, end: int) -> bool
    recommends v.WF(c)
{
    forall|node: int| Between(start, node, end) && c.ValidIdx(node) ==> v.highest_heard[node] > c.ids[node]
}

// ATOM 

pub open spec fn OnChordHeardDominatesIdInv(c: Constants, v: Variables) -> bool {
    &&& v.WF(c)
    &&& forall|start: int, end: int| IsChord(c, v, start, end) ==> OnChordHeardDominatesId(c, v, start, end)
}

// ATOM 

pub open spec fn Inv(c: Constants, v: Variables) -> bool {
    &&& v.WF(c)
    &&& OnChordHeardDominatesIdInv(c, v)
    &&& Safety(c, v)
}

// ATOM 

pub proof fn InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
{
}

// ATOM 

pub proof fn NextPreservesInv(c: Constants, v: Variables, v_prime: Variables)
    requires Inv(c, v), Next(c, v, v_prime)
    ensures Inv(c, v_prime)
{
}

// ATOM 

pub proof fn InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
{
}

}