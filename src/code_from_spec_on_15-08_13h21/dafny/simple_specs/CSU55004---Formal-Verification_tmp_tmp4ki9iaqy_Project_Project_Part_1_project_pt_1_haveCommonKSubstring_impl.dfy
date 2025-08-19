//ATOM
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
  requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
  /* code modified by LLM (iteration 2): Initialize res properly instead of just returning false */
  res := true;
  var i := 0;
  while i < |pre| && res
    invariant 0 <= i <= |pre|
    invariant res <==> (forall j :: 0 <= j < i ==> str[j] == pre[j])
  {
    if str[i] != pre[i] {
      res := false;
    }
    i := i + 1;
  }
}

//ATOM
//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
  requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
{
  res := false;
  var i := 0;
  while i <= |str| - |sub| && !res
    invariant 0 <= i <= |str| - |sub| + 1
    /* code modified by LLM (iteration 1): Added trigger to quantifier */
    invariant !res ==> forall j {:trigger str[j..j+|sub|]} :: 0 <= j < i ==> str[j..j+|sub|] != sub
  {
    if str[i..i+|sub|] == sub {
      res := true;
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 1): Added helper predicate with proper triggers */
predicate isSubstringExists(sub: string, str: string)
  requires |sub| > 0
{
  /* code modified by LLM (iteration 1): Added trigger to existential quantifier */
  |sub| <= |str| && exists i {:trigger str[i..i+|sub|]} :: 0 <= i <= |str| - |sub| && str[i..i+|sub|] == sub
}

//IMPL 
//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
  requires 0 < k <= |str1| && 0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
{
  /* code modified by LLM (iteration 1): Initialize found and fix the loop logic */
  found := false;
  var i := 0;
  
  /* code modified by LLM (iteration 1): Fixed loop bounds and corrected invariants */
  while i <= |str1| - k && !found
    invariant 0 <= i <= |str1| - k + 1
    invariant found ==> exists j {:trigger str1[j..j+k]} :: 0 <= j < i && isSubstringExists(str1[j..j+k], str2)
    /* code modified by LLM (iteration 1): Simplified invariant to avoid maintenance issues */
    invariant !found ==> forall j :: 0 <= j < i ==> (k <= |str2| ==> !isSubstringExists(str1[j..j+k], str2))
  {
    var substr := str1[i..i+k];
    /* code modified by LLM (iteration 1): Check precondition and call isSubstring */
    if k <= |str2| {
      var isCommon := isSubstring(substr, str2);
      if isCommon {
        found := true;
        /* code modified by LLM (iteration 1): Help prove the postcondition by establishing the connection */
        assert substr == str1[i..i+k];
        assert isSubstringExists(substr, str2);
      }
    }
    i := i + 1;
  }
}