method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
  /* code modified by LLM (iteration 4): fixed trigger syntax in postcondition */
  ensures result == (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|] :: main[i..i + |sub|])
{
  if |sub| == 0 {
    /* code modified by LLM (iteration 4): added assertion to help prove empty sublist case */
    assert sub == main[0..0];
    result := true;
    return;
  }
  
  if |sub| > |main| {
    /* code modified by LLM (iteration 4): added assertion to help prove impossible case */
    assert |main| - |sub| < 0;
    assert forall i :: 0 <= i <= |main| - |sub| :: false;
    result := false;
    return;
  }
  
  var i := 0;
  while i <= |main| - |sub|
    invariant 0 <= i <= |main| - |sub| + 1
    /* code modified by LLM (iteration 4): fixed loop invariant with proper trigger */
    invariant forall j :: 0 <= j < i && j <= |main| - |sub| ==> sub != main[j..j + |sub|] :: main[j..j + |sub|]
  {
    if sub == main[i..i + |sub|] {
      /* code modified by LLM (iteration 4): witness the existential quantifier */
      assert 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|];
      result := true;
      return;
    }
    /* code modified by LLM (iteration 4): add assertion before incrementing to help maintain invariant */
    assert sub != main[i..i + |sub|];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): strengthened final assertions with proper triggers */
  assert i == |main| - |sub| + 1;
  assert forall j :: 0 <= j <= |main| - |sub| ==> sub != main[j..j + |sub|] :: main[j..j + |sub|];
  result := false;
}