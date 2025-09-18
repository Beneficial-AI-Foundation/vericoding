// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): show non-negativity of seq length */
lemma LenSeqNonNegative(s: seq<int>) ensures |s| >= 0 {
  assert |s| >= 0;
}

/* helper modified by LLM (iteration 2): reflexivity of indexing */
lemma IndexReflexive(s: seq<int>, i: int) requires 0 <= i < |s| ensures s[i] == s[i] {
  assert s[i] == s[i];
}
// </vc-helpers>

// <vc-spec>
method ToArray(xs: seq<int>) returns (result: array<int>)
    ensures
        result.Length == |xs| &&
        forall i :: 0 <= i < |xs| ==> result[i] == xs[i]
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): implement ToArray without axioms and with proper loop invariants */
  result := new int[|xs|];
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant forall j :: 0 <= j < i ==> result[j] == xs[j]
  {
    result[i] := xs[i];
    i := i + 1;
  }
}
// </vc-code>
