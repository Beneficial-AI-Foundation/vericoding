// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): defined SmallestMissing recursively with helper functions */
function Contains(l: seq<nat>, n: nat): bool
  decreases |l|
{
  if |l| == 0 then false
  else if l[0] == n then true
  else if l[0] > n then false
  else Contains(l[1..], n)
}

function FindSmallestMissing(l: seq<nat>, candidate: nat): nat
  requires 0 <= candidate <= |l|
  decreases |l| - candidate
{
  if candidate < |l| && Contains(l, candidate) then
    FindSmallestMissing(l, candidate+1)
  else
    candidate
}

function SmallestMissing(l: seq<nat>): nat
{
  if |l| == 0 then 0
  else FindSmallestMissing(l, 0)
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
/* code modified by LLM (iteration 2): added asserts for lemma properties */
{
  assert SmallestMissing(l) !in l;
  assert forall candidate: nat :: candidate < SmallestMissing(l) ==> candidate in l;
}
// </vc-code>
