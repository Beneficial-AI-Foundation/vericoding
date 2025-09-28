// <vc-preamble>

predicate BelowThreshold(l: seq<int>, t: int)
{
    forall i :: 0 <= i < |l| ==> l[i] < t
}
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Fixed helper lemma and predicate */
predicate BelowThresholdHelper(l: seq<int>, t: int, index: int)
  requires 0 <= index <= |l|
{
  forall i :: index <= i < |l| ==> l[i] < t
}

lemma BelowThresholdHelperEmpty(l: seq<int>, t: int)
  ensures BelowThresholdHelper(l, t, |l|)
{
}

lemma BelowThresholdHelperStep(l: seq<int>, t: int, i: int)
  requires 0 <= i < |l|
  requires BelowThresholdHelper(l, t, i+1)
  ensures BelowThresholdHelper(l, t, i) <==> l[i] < t
{
}

// </vc-helpers>

// <vc-spec>
method CheckBelowThreshold(l: seq<int>, t: int) returns (result: bool)
    ensures result == BelowThreshold(l, t)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed loop logic with proper invariant maintenance */
  var i := |l|;
  result := true;
  
  while i > 0
    invariant 0 <= i <= |l|
    invariant result == BelowThresholdHelper(l, t, i)
  {
    i := i - 1;
    if l[i] >= t {
      result := false;
      break;
    }
    BelowThresholdHelperStep(l, t, i);
  }
}
// </vc-code>
