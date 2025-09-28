// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SmallestMissingHelper(l: seq<nat>, i: nat): nat
  decreases |l| - i
{
  /* helper modified by LLM (iteration 4): corrected formatting to single line for if expression */
  if i == |l| then i else if l[i] == i then SmallestMissingHelper(l, i + 1) else i
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
  /* code modified by LLM (iteration 5): added missing semicolon after function call */
  SmallestMissingHelper(l, 0);
}
// </vc-code>
