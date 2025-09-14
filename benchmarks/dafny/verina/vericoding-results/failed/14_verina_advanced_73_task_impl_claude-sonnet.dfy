// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed postconditions and added proper implementation */
function SmallestMissingImpl(l: seq<nat>): nat
{
  SmallestMissingRec(l, 0)
}

function SmallestMissingRec(l: seq<nat>, start: nat): nat
  decreases |l|
{
  if start >= |l| then start
  else if start !in l then start
  else SmallestMissingRec(l, start + 1)
}

lemma SmallestMissingRecCorrect(l: seq<nat>, start: nat)
  requires forall i, j :: 0 <= i < j < |l| ==> l[i] < l[j]
  ensures SmallestMissingRec(l, start) !in l || SmallestMissingRec(l, start) < start
  ensures forall candidate: nat :: start <= candidate < SmallestMissingRec(l, start) ==> candidate in l
  decreases |l|
{
  var result := SmallestMissingRec(l, start);
  if start >= |l| {
    // result == start >= |l|, so result not in l since all elements < |l|
    assert result >= |l|;
    assert forall x :: x in l ==> x < |l|;
  } else if start !in l {
    // result == start and start !in l
  } else {
    SmallestMissingRecCorrect(l, start + 1);
    assert result == SmallestMissingRec(l, start + 1);
    assert result !in l || result < start + 1;
    if result >= start + 1 {
      assert result !in l;
    }
  }
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
  /* code modified by LLM (iteration 5): proper implementation using corrected helper */
  SmallestMissingRecCorrect(l, 0);
  
  var result := SmallestMissingImpl(l);
  
  // Prove result !in l
  assert result !in l || result < 0;
  assert result >= 0; // natural numbers are >= 0
  assert result !in l;
  
  // Prove all candidates < result are in l
  forall candidate: nat | candidate < result
    ensures candidate in l
  {
    assert 0 <= candidate < result;
    assert candidate in l; // from helper postcondition
  }
}
// </vc-code>
