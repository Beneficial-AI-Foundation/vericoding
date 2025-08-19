//IMPL 
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
  ensures result <==> (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
{
  if |sub| == 0 {
    /* code modified by LLM (iteration 4): Fixed empty subsequence case with proper bounds check */
    if |main| >= 0 {
      assert sub == main[0..0];
      assert exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|];
      result := true;
    } else {
      result := false;
    }
    return;
  }
  
  if |sub| > |main| {
    /* code modified by LLM (iteration 4): Fixed case when sub is longer than main */
    assert |main| - |sub| < 0;
    assert forall i :: 0 <= i <= |main| - |sub| ==> false;
    assert !(exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|]);
    result := false;
    return;
  }
  
  var i := 0;
  /* code modified by LLM (iteration 4): Fixed loop invariants with correct bounds and termination */
  while i <= |main| - |sub|
    invariant 0 <= i <= |main| - |sub| + 1
    invariant forall j :: 0 <= j < i ==> sub != main[j..j + |sub|]
    decreases |main| - |sub| + 1 - i
  {
    if sub == main[i..i + |sub|] {
      /* code modified by LLM (iteration 4): Simplified assertion for found case */
      assert 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|];
      result := true;
      return;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): Fixed final case with proper quantifier reasoning */
  assert i > |main| - |sub|;
  assert forall j :: 0 <= j <= |main| - |sub| ==> j < i;
  assert forall j :: 0 <= j <= |main| - |sub| ==> sub != main[j..j + |sub|];
  result := false;
}