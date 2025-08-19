method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
  ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
{
  if |sub| > |main| {
    result := false;
    return;
  }
  
  var i := 0;
  while i <= |main| - |sub|
    invariant 0 <= i <= |main| - |sub| + 1
    /* code modified by LLM (iteration 2): fixed invariant maintenance by ensuring proper bounds and proof order */
    invariant forall j {:trigger main[j..j + |sub|]} :: 0 <= j < i && j + |sub| <= |main| ==> sub != main[j..j + |sub|]
  {
    /* code modified by LLM (iteration 2): moved bounds check before comparison to ensure valid slice */
    assert i + |sub| <= |main|;
    
    if sub == main[i..i + |sub|] {
      result := true;
      return;
    }
    
    /* code modified by LLM (iteration 2): assert the negation to help maintain the invariant */
    assert sub != main[i..i + |sub|];
    /* code modified by LLM (iteration 2): explicit assertion to help prove invariant after increment */
    assert forall j :: 0 <= j <= i && j + |sub| <= |main| ==> sub != main[j..j + |sub|];
    
    i := i + 1;
  }
  
  result := false;
}