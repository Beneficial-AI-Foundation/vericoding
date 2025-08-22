//ATOM
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
  requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
  /* code modified by LLM (iteration 1): Added complete implementation for isPrefix */
  res := true;
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant res == (forall k :: 0 <= k < i ==> str[k] == pre[k])
    decreases |pre| - i
  {
    if str[i] != pre[i] {
      res := false;
      return;
    }
    i := i + 1;
  }
}


//ATOM

//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
  requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
{
  /* code modified by LLM (iteration 1): Added complete implementation for isSubstring */
  res := false;
  var i := 0;
  while i <= |str| - |sub|
    invariant 0 <= i <= |str| - |sub| + 1
    invariant !res ==> (forall k :: 0 <= k < i ==> str[k..k+|sub|] != sub)
    decreases |str| - |sub| - i + 1
  {
    if str[i..i+|sub|] == sub {
      res := true;
      return;
    }
    i := i + 1;
  }
}


//IMPL haveCommonKSubstring

//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
  requires 0 < k <= |str1| && 0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
{
  found := false;
  
  // Check all possible substrings of length k in str1
  var i := 0;
  /* code modified by LLM (iteration 3): Simplified and corrected loop invariants */
  while i <= |str1| - k && !found
    invariant 0 <= i <= |str1| - k + 1
    invariant !found ==> (forall x :: 0 <= x < i ==> 
      (forall y :: 0 <= y <= |str2| - k ==> str1[x..x+k] != str2[y..y+k]))
    decreases |str1| - k - i + 1
  {
    // Extract substring of length k starting at position i in str1
    var sub1 := str1[i..i+k];
    
    // Check if this substring exists in str2
    var j := 0;
    /* code modified by LLM (iteration 3): Fixed inner loop with proper invariant */
    while j <= |str2| - k && !found
      invariant 0 <= j <= |str2| - k + 1
      invariant !found ==> (forall y :: 0 <= y < j ==> str2[y..y+k] != sub1)
      invariant sub1 == str1[i..i+k]
      decreases |str2| - k - j + 1
    {
      var sub2 := str2[j..j+k];
      if sub1 == sub2 {
        found := true;
        /* code modified by LLM (iteration 3): Added assertion to help verification */
        assert str1[i..i+k] == str2[j..j+k];
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}