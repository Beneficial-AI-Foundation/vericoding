// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SmallestMissing(l: seq<nat>): nat {
  if |l| == 0 then
    0
  else if l[0] != 0 then
    0
  else {
    var candidate := 0;
    while candidate < |l| && l[candidate] == candidate
      invariant 0 <= candidate <= |l|
      invariant forall i :: 0 <= i < candidate ==> l[i] == i
    {
      candidate := candidate + 1;
    }
    candidate
  }
}

/* helper modified by LLM (iteration 5): Fixed while loop syntax */
lemma SmallestMissingSpecSatisfied(l: seq<nat>)
    requires forall i, j :: 0 <= i < j < |l| ==> l[i] < l[j]
    ensures SmallestMissing(l) !in l
    ensures forall candidate: nat :: candidate < SmallestMissing(l) ==> candidate in l
{
  var sm := SmallestMissing(l);
  assert sm !in l;
  assert forall x :: x < sm ==> x in l;
}
// </vc-helpers>

// <vc-spec>
function SmallestMissing(l: seq<nat>): nat

lemma SmallestMissingSpecSatisfied(l: seq<nat>)
    requires forall i, j :: 0 <= i < j < |l| ==> l[i] < l[j]
    ensures SmallestMissing(l) !in l
    ensures forall candidate: nat :: candidate < SmallestMissing(l) ==> candidate in l
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Empty method body as implementation is in helpers */
}
// </vc-code>
