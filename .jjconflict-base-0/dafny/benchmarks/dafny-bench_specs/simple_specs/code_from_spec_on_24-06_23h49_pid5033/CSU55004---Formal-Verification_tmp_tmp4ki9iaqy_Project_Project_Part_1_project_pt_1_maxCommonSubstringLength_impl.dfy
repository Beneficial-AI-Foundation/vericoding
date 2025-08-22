//ATOM
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
  requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
  res := false;
  return res;
}


//ATOM

//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
  requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
{
  res := false;
}


//ATOM

//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
  requires 0 < k <= |str1| && 0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
{
  found := false;
}


//IMPL maxCommonSubstringLength

//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
method maxCommonSubstringLength(str1:string, str2:string) returns(len:nat)
  requires 0 < |str1| && 0 < |str2|
{
  len := 0;
  var maxLen := if |str1| <= |str2| then |str1| else |str2|;
  var k := 1;
  
  /* code modified by LLM (iteration 1): Fixed loop invariants and ensured proper bounds checking */
  while k <= maxLen
    invariant 0 <= len <= k - 1
    invariant 1 <= k <= maxLen + 1
    invariant len <= maxLen
  {
    var hasCommon := haveCommonKSubstring(k, str1, str2);
    if hasCommon {
      len := k;
    }
    k := k + 1;
  }
}