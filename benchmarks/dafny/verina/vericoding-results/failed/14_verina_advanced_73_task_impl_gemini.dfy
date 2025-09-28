// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): defining SmallestMissing using a 'least' expression */
function SmallestMissing(l: seq<nat>): nat
{
  least k: nat | k !in l
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
/* code modified by LLM (iteration 5): empty body, proof follows from the function definition */
{
}
// </vc-code>
