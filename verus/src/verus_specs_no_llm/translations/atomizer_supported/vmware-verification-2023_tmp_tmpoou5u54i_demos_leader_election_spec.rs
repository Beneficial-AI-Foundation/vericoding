// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn ValidIdx(i: int) -> bool {
    0<=i<ids.len()
}
spec fn UniqueIds() -> bool {
    (forall i, j | ValidIdx(i) && ValidIdx(j) && ids.spec_index(i)==ids.spec_index(j) :: i == j)
}
spec fn WF() -> bool {
    && 0 < ids.len()
    && UniqueIds()
}
spec fn WF(c: Constants) -> bool {
    && c.WF()
    && highest_heard.len() == c.ids.len()
}
spec fn Init(c: Constants, v: Variables) -> bool {
    && v.WF(c)
  && c.UniqueIds()
     // Everyone begins having heard about nobody, not even themselves.
  && (forall i | c.ValidIdx(i) :: v.highest_heard.spec_index(i) == -1)
}
spec fn Transmission(c: Constants, v: Variables, v': Variables, srcidx: nat) -> bool {
    && v.WF(c)
  && v'.WF(c)
  && c.ValidIdx(srcidx)

  // Neighbor address in ring.
  && var dstidx := NextIdx(c, srcidx);

  // srcidx sends the max of its highest_heard value && its own id.
  && var message := max(v.highest_heard.spec_index(srcidx), c.ids.spec_index(srcidx));

  // dstidx only overwrites its highest_heard if the message is higher.
  && var dst_new_max := max(v.highest_heard.spec_index(dstidx), message);
  // XXX Manos: How could this have been a bug!? How could a srcidx, having sent message X, ever send message Y < X!?

  && v' == v.(highest_heard := v.highest_heard.spec_index(dstidx := dst_new_max))
}
spec fn NextStep(c: Constants, v: Variables, v': Variables, step: Step) -> bool {
    match step {
    case TransmissionStep(srcidx) => Transmission(c, v, v', srcidx)
}
spec fn Next(c: Constants, v: Variables, v': Variables) -> bool {
    exists step :: NextStep(c, v, v', step)
}
spec fn IsLeader(c: Constants, v: Variables, i: int)
  requires v.WF(c) -> bool {
    && c.ValidIdx(i)
  && v.highest_heard.spec_index(i) == c.ids.spec_index(i)
}
spec fn Safety(c: Constants, v: Variables)
  requires v.WF(c) -> bool {
    forall i, j | IsLeader(c, v, i) && IsLeader(c, v, j) :: i == j
}
spec fn IsChord(c: Constants, v: Variables, start: int, end: int) -> bool {
    && v.WF(c)
  && c.ValidIdx(start)
  && c.ValidIdx(end)
  && c.ids.spec_index(start) == v.highest_heard.spec_index(end)
}
spec fn Between(start: int, node: int, end: int) -> bool {
    if start < end
  then start < node < end // not wrapped
  else node < end || start < node // wrapped
}
spec fn OnChordHeardDominatesId(c: Constants, v: Variables, start: int, end: int)
  requires v.WF(c) -> bool {
    forall node | Between(start, node, end) && c.ValidIdx(node)
    :: v.highest_heard.spec_index(node) > c.ids.spec_index(node)
}
spec fn OnChordHeardDominatesIdInv(c: Constants, v: Variables) -> bool {
    && v.WF(c)
  && (forall start, end
       | IsChord(c, v, start, end)
       :: OnChordHeardDominatesId(c, v, start, end)
          )
}
spec fn Inv(c: Constants, v: Variables) -> bool {
    && v.WF(c)
  && OnChordHeardDominatesIdInv(c, v)
  && Safety(c, v)
}

}