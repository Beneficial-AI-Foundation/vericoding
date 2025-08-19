method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
  requires n >= 0
  ensures |r| == |l|
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
{
  if |l| == 0 {
    r := l;
  } else {
    var effectiveN := n % |l|;
    /* code modified by LLM (iteration 3): Simplified rotation implementation */
    r := l[|l| - effectiveN..] + l[..|l| - effectiveN];
    
    /* code modified by LLM (iteration 3): Added key lemma to help with modular arithmetic */
    assert forall k :: 0 <= k ==> (k - n + |l|) % |l| == (k - effectiveN + |l|) % |l|;
    
    /* code modified by LLM (iteration 3): Fixed quantifier syntax with proper bounds */
    assert forall i :: 0 <= i < effectiveN ==> r[i] == l[|l| - effectiveN + i];
    assert forall i :: effectiveN <= i < |l| ==> r[i] == l[i - effectiveN];
    
    /* code modified by LLM (iteration 3): Fixed quantifier syntax for modular arithmetic */
    assert forall i :: 0 <= i < effectiveN ==> (i - effectiveN + |l|) % |l| == |l| - effectiveN + i;
    assert forall i :: effectiveN <= i < |l| ==> (i - effectiveN + |l|) % |l| == i - effectiveN;
  }
}