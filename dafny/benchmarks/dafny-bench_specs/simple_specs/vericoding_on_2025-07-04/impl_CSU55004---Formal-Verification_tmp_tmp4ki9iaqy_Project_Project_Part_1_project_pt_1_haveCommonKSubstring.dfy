//ATOM
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
  requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
  res := true;
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant res <==> forall j :: 0 <= j < i ==> str[j] == pre[j]
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
  res := false;
  var i := 0;
  while i <= |str| - |sub|
    invariant 0 <= i <= |str| - |sub| + 1
    invariant res <==> exists j :: 0 <= j < i && forall k :: 0 <= k < |sub| ==> str[j + k] == sub[k]
  {
    var match := true;
    var j := 0;
    while j < |sub| && match
      invariant 0 <= j <= |sub|
      invariant match <==> forall k :: 0 <= k < j ==> str[i + k] == sub[k]
    {
      if str[i + j] != sub[j] {
        match := false;
      }
      j := j + 1;
    }
    if match {
      res := true;
      return;
    }
    i := i + 1;
  }
}

//IMPL 
//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
  requires 0 < k <= |str1| && 0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
{
  found := false;
  var i := 0;
  while i <= |str1| - k
    /* code modified by LLM (iteration 1): Simplified invariant to focus on bounds and found condition */
    invariant 0 <= i <= |str1| - k + 1
    invariant found ==> exists i1, j1 :: 0 <= i1 <= |str1| - k && 0 <= j1 <= |str2| - k && 
                        forall l :: 0 <= l < k ==> str1[i1 + l] == str2[j1 + l]
  {
    var j := 0;
    while j <= |str2| - k
      /* code modified by LLM (iteration 1): Simplified inner loop invariant */
      invariant 0 <= j <= |str2| - k + 1
      invariant found ==> exists i1, j1 :: 0 <= i1 <= |str1| - k && 0 <= j1 <= |str2| - k && 
                          forall l :: 0 <= l < k ==> str1[i1 + l] == str2[j1 + l]
    {
      var match := true;
      var l := 0;
      while l < k && match
        invariant 0 <= l <= k
        invariant match <==> forall m :: 0 <= m < l ==> str1[i + m] == str2[j + m]
      {
        if str1[i + l] != str2[j + l] {
          match := false;
        }
        l := l + 1;
      }
      if match {
        found := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}