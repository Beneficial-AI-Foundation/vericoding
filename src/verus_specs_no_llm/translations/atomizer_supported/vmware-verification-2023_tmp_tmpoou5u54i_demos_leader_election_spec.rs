// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn ValidIdx(i: int) -> bool {
    0<=i<ids.len()
}

spec fn UniqueIds() -> bool {
    (forall|i: int, j | ValidIdx(i) and ValidIdx(j) and ids[i]==ids[j]: int| i == j)
}

spec fn WF() -> bool {
    and 0 < ids.len()
    and UniqueIds()
}

spec fn WF(c: Constants) -> bool {
    and c.WF()
    and highest_heard.len() == c.ids.len()
}

spec fn Init(c: Constants, v: Variables) -> bool {
    and v.WF(c)
  and c.UniqueIds()
     // Everyone begins having heard about nobody, not even themselves.
  and (forall|i | c.ValidIdx(i): int| v.highest_heard[i] == -1)
}

spec fn Transmission(c: Constants, v: Variables, v': Variables, srcidx: nat) -> bool {
    and v.WF(c)
  and v'.WF(c)
  and c.ValidIdx(srcidx)

  // Neighbor address in ring.
  and var dstidx := NextIdx(c, srcidx);

  // srcidx sends the max of its highest_heard value and its own id.
  and var message := max(v.highest_heard[srcidx], c.ids[srcidx]);

  // dstidx only overwrites its highest_heard if the message is higher.
  and var dst_new_max := max(v.highest_heard[dstidx], message);
  // XXX Manos: How could this have been a bug!? How could a srcidx, having sent message X, ever send message Y < X!?

  and v' == v.(highest_heard := v.highest_heard[dstidx := dst_new_max])
}

spec fn NextStep(c: Constants, v: Variables, v': Variables, step: Step) -> bool {
    match step {
    case TransmissionStep(srcidx) => Transmission(c, v, v', srcidx)
}

spec fn Next(c: Constants, v: Variables, v': Variables) -> bool {
    exists|step: int| NextStep(c, v, v', step)
}

spec fn IsLeader(c: Constants, v: Variables, i: int)
  requires v.WF(c) -> bool {
    and c.ValidIdx(i)
  and v.highest_heard[i] == c.ids[i]
}

spec fn Safety(c: Constants, v: Variables)
  requires v.WF(c) -> bool {
    forall|i: int, j | IsLeader(c: int, v: int, i) and IsLeader(c: int, v: int, j): int| i == j
}

spec fn IsChord(c: Constants, v: Variables, start: int, end: int) -> bool {
    and v.WF(c)
  and c.ValidIdx(start)
  and c.ValidIdx(end)
  and c.ids[start] == v.highest_heard[end]
}

spec fn Between(start: int, node: int, end: int) -> bool {
    if start < end
  then start < node < end // not wrapped
  else node < end or start < node // wrapped
}

spec fn OnChordHeardDominatesId(c: Constants, v: Variables, start: int, end: int)
  requires v.WF(c) -> bool {
    forall|node | Between(start: int, node: int, end) and c.ValidIdx(node): int| v.highest_heard[node] > c.ids[node]
}

spec fn OnChordHeardDominatesIdInv(c: Constants, v: Variables) -> bool {
    and v.WF(c)
  and (forall|start: int, end
       | IsChord(c: int, v: int, start: int, end): int| OnChordHeardDominatesId(c, v, start, end)
          )
}

spec fn Inv(c: Constants, v: Variables) -> bool {
    and v.WF(c)
  and OnChordHeardDominatesIdInv(c, v)
  and Safety(c, v)
}

}