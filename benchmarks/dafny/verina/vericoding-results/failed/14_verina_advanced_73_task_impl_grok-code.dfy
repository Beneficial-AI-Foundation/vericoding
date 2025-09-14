// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed syntax error by removing invalid word 'anatomy' */
function SmallestMissingAux(l: seq<nat>, start: nat): nat
decreases |l|
{
  if |l| == 0 then start
  else if l[0] > start then start
  else SmallestMissingAux(l[1..], l[0] + 1)
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
/* code modified by LLM (iteration 5): added semicolon and result assignment to fix compilation error */
  result := SmallestMissingAux(l, 0);
}
// </vc-code>
