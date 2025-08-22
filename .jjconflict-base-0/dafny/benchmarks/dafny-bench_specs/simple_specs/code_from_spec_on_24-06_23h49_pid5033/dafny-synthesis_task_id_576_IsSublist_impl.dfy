//IMPL 
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
  ensures result <==> (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
{
  /* code modified by LLM (iteration 4): Handle empty subsequence case correctly */
  if |sub| == 0 {
    /* code modified by LLM (iteration 4): Empty subsequence is always found at position 0 */
    assert sub == main[0..0];
    assert 0 <= 0 <= |main| - 0;
    result := true;
    return;
  }
  
  /* code modified by LLM (iteration 4): Handle case where subsequence is larger than main sequence */
  if |sub| > |main| {
    /* code modified by LLM (iteration 4): Prove no valid position exists when sub is too large */
    assert |main| - |sub| < 0;
    assert !(exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|]);
    result := false;
    return;
  }
  
  var j := 0;
  /* code modified by LLM (iteration 4): Fixed loop to check all valid positions */
  while j <= |main| - |sub|
    invariant 0 <= j <= |main| - |sub| + 1
    invariant forall k :: 0 <= k < j ==> sub != main[k..k + |sub|]
  {
    /* code modified by LLM (iteration 4): Check if subsequence matches at current position */
    if sub == main[j..j + |sub|] {
      /* code modified by LLM (iteration 4): Establish existence of matching position */
      assert 0 <= j <= |main| - |sub| && sub == main[j..j + |sub|];
      result := true;
      return;
    }
    j := j + 1;
  }
  
  /* code modified by LLM (iteration 4): After loop, j = |main| - |sub| + 1, so all positions checked */
  assert j == |main| - |sub| + 1;
  assert forall k :: 0 <= k < j ==> sub != main[k..k + |sub|];
  /* code modified by LLM (iteration 4): Since j = |main| - |sub| + 1, the range 0 <= k < j covers all valid positions */
  assert forall k :: 0 <= k <= |main| - |sub| ==> sub != main[k..k + |sub|];
  assert !(exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|]);
  result := false;
}