// Each node's identifier (address)
// ATOM 
// Each node's identifier (address)
datatype Constants = Constants(ids: seq<nat>) {
  predicate ValidIdx(i: int) {
    0<=i<|ids|
  }
  ghost predicate UniqueIds() {

    (forall i, j | ValidIdx(i) && ValidIdx(j) && ids[i]==ids[j] :: i == j)
  }
  ghost predicate WF() {

    && 0 < |ids|
    && UniqueIds()
  }
}





}

// The highest other identifier this node has heard about.
// ATOM 

// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<int>) {
  ghost predicate WF(c: Constants)
  {
    && c.WF()
    && |highest_heard| == |c.ids|
  }
}

}

// ATOM 

ghost predicate Init(c: Constants, v: Variables)
{
  && v.WF(c)
  && c.UniqueIds()
     // Everyone begins having heard about nobody, not even themselves.
  && (forall i | c.ValidIdx(i) :: v.highest_heard[i] == -1)
}


// ATOM 

function max(a: int, b: int) : int {
  if a > b then a else b
}


// ATOM 

function NextIdx(c: Constants, idx: nat) : nat
  requires c.WF()
  requires c.ValidIdx(idx)
{
  if idx + 1 == |c.ids| then 0 else idx + 1
}


// ATOM 

ghost predicate Transmission(c: Constants, v: Variables, v': Variables, srcidx: nat)
{
  && v.WF(c)
  && v'.WF(c)
  && c.ValidIdx(srcidx)

  // Neighbor address in ring.
  && var dstidx := NextIdx(c, srcidx);

  // srcidx sends the max of its highest_heard value and its own id.
  && var message := max(v.highest_heard[srcidx], c.ids[srcidx]);

  // dstidx only overwrites its highest_heard if the message is higher.
  && var dst_new_max := max(v.highest_heard[dstidx], message);
  // XXX Manos: How could this have been a bug!? How could a srcidx, having sent message X, ever send message Y < X!?

  && v' == v.(highest_heard := v.highest_heard[dstidx := dst_new_max])
}


// ATOM 

datatype Step = TransmissionStep(srcidx: nat)
// ATOM 

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
{
  match step {
    case TransmissionStep(srcidx) => Transmission(c, v, v', srcidx)
  }
}


// ATOM 

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  exists step :: NextStep(c, v, v', step)
}


//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

// ATOM 

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

ghost predicate IsLeader(c: Constants, v: Variables, i: int)
  requires v.WF(c)
{
  && c.ValidIdx(i)
  && v.highest_heard[i] == c.ids[i]
}


// ATOM 

ghost predicate Safety(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j | IsLeader(c, v, i) && IsLeader(c, v, j) :: i == j
}


//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

// ATOM 

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

ghost predicate IsChord(c: Constants, v: Variables, start: int, end: int)
{
  && v.WF(c)
  && c.ValidIdx(start)
  && c.ValidIdx(end)
  && c.ids[start] == v.highest_heard[end]
}


// ATOM 

ghost predicate Between(start: int, node: int, end: int)
{
  if start < end
  then start < node < end // not wrapped
  else node < end || start < node // wrapped
}


// ATOM 

ghost predicate OnChordHeardDominatesId(c: Constants, v: Variables, start: int, end: int)
  requires v.WF(c)
{
  forall node | Between(start, node, end) && c.ValidIdx(node)
    :: v.highest_heard[node] > c.ids[node]
}


// ATOM 

ghost predicate OnChordHeardDominatesIdInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && (forall start, end
       | IsChord(c, v, start, end)
       :: OnChordHeardDominatesId(c, v, start, end)
          )
}


// ATOM 

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && OnChordHeardDominatesIdInv(c, v)
  && Safety(c, v)
}


// ATOM 

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
}


// ATOM 

lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  var step :| NextStep(c, v, v', step);
  var srcidx := step.srcidx;
  var dstidx := NextIdx(c, srcidx);
  var message := max(v.highest_heard[srcidx], c.ids[srcidx]);
  var dst_new_max := max(v.highest_heard[dstidx], message);

  forall start, end
    | IsChord(c, v', start, end)
    ensures OnChordHeardDominatesId(c, v', start, end)
  {
    forall node | Between(start, node, end) && c.ValidIdx(node)
      ensures v'.highest_heard[node] > c.ids[node]
    {
      if dstidx == end {
        // maybe this chord just sprung into existence
        if v'.highest_heard[end] == v.highest_heard[end] {
          // no change --
        } else if v'.highest_heard[end] == c.ids[srcidx] {
        } else if v'.highest_heard[end] == v.highest_heard[srcidx] {
        }
      } else {
        // this chord was already here
      }
    }
  }

  forall i, j | IsLeader(c, v', i) && IsLeader(c, v', j) ensures i == j {
  }
}


// ATOM 

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{
}




