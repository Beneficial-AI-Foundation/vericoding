//ATOM isPrefix
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
  requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
  /* code modified by LLM (iteration 2): Fixed implementation to actually check if pre is a prefix of str */
  res := true;
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant res ==> forall k :: 0 <= k < i ==> str[k] == pre[k]
  {
    if str[i] != pre[i] {
      res := false;
      return;
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 4): Added helper predicate for substring verification */
predicate isPrefixAt(sub: string, str: string, pos: int)
  requires 0 <= pos <= |str|
{
  pos + |sub| <= |str| && forall k :: 0 <= k < |sub| ==> str[pos + k] == sub[k]
}

//IMPL isSubstring
//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
  requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
{
  res := false;
  var i := 0;
  
  /* code modified by LLM (iteration 4): Fixed loop bounds and invariants for proper verification */
  while i <= |str| - |sub|
    invariant 0 <= i <= |str| - |sub| + 1
    invariant !res ==> forall k :: 0 <= k < i ==> !isPrefixAt(sub, str, k)
  {
    var j := 0;
    var match := true;
    
    /* code modified by LLM (iteration 4): Fixed inner loop with proper bounds checking */
    while j < |sub| && match
      invariant 0 <= j <= |sub|
      invariant i + |sub| <= |str|
      invariant match ==> forall k :: 0 <= k < j ==> str[i + k] == sub[k]
      invariant !match ==> exists k :: 0 <= k < j && str[i + k] != sub[k]
    {
      if str[i + j] != sub[j] {
        match := false;
      }
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 4): Simplified match checking */
    if match {
      assert j == |sub|;
      assert forall k :: 0 <= k < |sub| ==> str[i + k] == sub[k];
      assert isPrefixAt(sub, str, i);
      res := true;
      return;
    }
    
    assert !isPrefixAt(sub, str, i);
    i := i + 1;
  }
}