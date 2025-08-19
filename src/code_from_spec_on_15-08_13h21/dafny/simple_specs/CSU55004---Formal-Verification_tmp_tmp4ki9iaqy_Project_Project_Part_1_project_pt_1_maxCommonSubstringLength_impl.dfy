//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
  requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
  /* code modified by LLM (iteration 1): implemented proper prefix checking logic */
  res := true;
  var i := 0;
  while i < |pre|
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
  /* code modified by LLM (iteration 1): initialized res parameter and implemented substring checking logic */
  res := false;
  var i := 0;
  while i <= |str| - |sub|
    decreases |str| - |sub| - i + 1
  {
    var isMatch := true;
    var j := 0;
    while j < |sub| && isMatch
      decreases |sub| - j
    {
      if str[i + j] != sub[j] {
        isMatch := false;
      }
      j := j + 1;
    }
    if isMatch {
      res := true;
      return;
    }
    i := i + 1;
  }
}


//ATOM

//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
  requires 0 < k <= |str1| && 0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
{
  /* code modified by LLM (iteration 1): initialized found parameter and implemented common k-substring checking logic */
  found := false;
  var i := 0;
  while i <= |str1| - k
    decreases |str1| - k - i + 1
  {
    var j := 0;
    while j <= |str2| - k
      decreases |str2| - k - j + 1
    {
      var isMatch := true;
      var pos := 0;
      while pos < k && isMatch
        decreases k - pos
      {
        if str1[i + pos] != str2[j + pos] {
          isMatch := false;
        }
        pos := pos + 1;
      }
      if isMatch {
        found := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}


//IMPL 

//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
method maxCommonSubstringLength(str1:string, str2:string) returns(len:nat)
  requires 0 < |str1| && 0 < |str1|
{
  len := 0;
  var maxLen := if |str1| < |str2| then |str1| else |str2|;
  var currentLen := maxLen;
  
  while currentLen > len
    decreases currentLen
  {
    var i := 0;
    while i <= |str1| - currentLen
      decreases |str1| - currentLen - i
    {
      var j := 0;
      while j <= |str2| - currentLen
        decreases |str2| - currentLen - j
      {
        /* code modified by LLM (iteration 1): renamed 'match' to 'isMatch' since 'match' is a reserved keyword in Dafny */
        var isMatch := true;
        var k := 0;
        /* code modified by LLM (iteration 1): moved decreases clause to while loop header and fixed variable reference */
        while k < currentLen && isMatch
          decreases currentLen - k
        {
          if str1[i + k] != str2[j + k] {
            /* code modified by LLM (iteration 1): updated variable name from 'match' to 'isMatch' */
            isMatch := false;
          }
          k := k + 1;
        }
        if isMatch {
          len := currentLen;
          return;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    currentLen := currentLen - 1;
  }
}