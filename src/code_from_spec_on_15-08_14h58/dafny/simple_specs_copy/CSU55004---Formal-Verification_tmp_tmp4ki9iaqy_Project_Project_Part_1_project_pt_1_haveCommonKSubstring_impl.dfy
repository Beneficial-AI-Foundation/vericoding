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
  /* code modified by LLM (iteration 1): Added missing assignment to res parameter to fix definite-assignment error */
  res := false;
}

//IMPL 
//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
  requires 0 < k <= |str1| && 0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
{
  found := false;
  
  var i := 0;
  while i <= |str1| - k
    invariant 0 <= i <= |str1| - k + 1
  {
    var sub1 := str1[i..i+k];
    var j := 0;
    while j <= |str2| - k
      invariant 0 <= j <= |str2| - k + 1
    {
      var sub2 := str2[j..j+k];
      if sub1 == sub2 {
        found := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}