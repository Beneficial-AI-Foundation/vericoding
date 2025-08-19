predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}


//ATOM


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}


//ATOM

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==> isNotSubstringPred(str1[i1..j1],str2)
}


//ATOM
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| && isPrefixPred(sub, str[i..]))
}


//ATOM

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
  res := false;
  /* code modified by LLM (iteration 1): Removed assume statement and implemented proper logic */
  for i := 0 to |str| + 1
    invariant 0 <= i <= |str| + 1
    invariant res <==> exists j :: 0 <= j < i && isPrefixPred(sub, str[j..])
  {
    if isPrefixPred(sub, str[i..]) {
      res := true;
      return res;
    }
  }
  return res;
}


//ATOM

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}


//ATOM

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  /* code modified by LLM (iteration 1): Removed assume statements and implemented proper logic */
  if |pre| > |str| {
    res := false;
    return res;
  }
  
  res := (pre == str[..|pre|]);
  return res;
}


//ATOM

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}


//ATOM

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found <==> haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
  /* code modified by LLM (iteration 2): Fixed loop invariant and postcondition proof */
  found := false;
  
  if k > |str1| {
    return found;
  }
  
  var i1 := 0;
  while i1 <= |str1| - k
    invariant 0 <= i1 <= |str1| - k + 1
    invariant !found ==> forall j :: 0 <= j < i1 ==> !isSubstringPred(str1[j..j+k], str2)
    invariant found ==> exists j :: 0 <= j < i1 && isSubstringPred(str1[j..j+k], str2)
  {
    var substring := str1[i1..i1+k];
    var isCommon := isSubstring(substring, str2);
    if isCommon {
      found := true;
      /* code modified by LLM (iteration 2): Added assertion to help prove postcondition */
      assert isSubstringPred(str1[i1..i1+k], str2);
      assert haveCommonKSubstringPred(k, str1, str2);
      return found;
    }
    /* code modified by LLM (iteration 2): Added assertion to help maintain loop invariant */
    assert !isSubstringPred(str1[i1..i1+k], str2);
    i1 := i1 + 1;
  }
  
  /* code modified by LLM (iteration 2): Added assertion to help prove postcondition */
  assert forall j :: 0 <= j <= |str1| - k ==> !isSubstringPred(str1[j..j+k], str2);
  assert !haveCommonKSubstringPred(k, str1, str2);
  return found;
}


//ATOM

//IMPL 

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
  /* code modified by LLM (iteration 2): Handle edge case and ensure empty string case */
  if |str1| == 0 {
    len := 0;
    /* code modified by LLM (iteration 2): Added assertion for empty string case */
    assert haveCommonKSubstringPred(0, str1, str2);
    return;
  }
  
  /* code modified by LLM (iteration 2): Fixed loop to ensure postcondition */
  len := |str1|;
  while len > 0
    invariant 0 <= len <= |str1|
    invariant forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2)
  {
    var found := haveCommonKSubstring(len, str1, str2);
    if found {
      /* code modified by LLM (iteration 2): Added assertion to help prove postcondition */
      assert haveCommonKSubstringPred(len, str1, str2);
      return;
    }
    len := len - 1;
  }
  
  /* code modified by LLM (iteration 2): Handle len = 0 case properly */
  len := 0;
  /* code modified by LLM (iteration 2): Added assertion that empty string is always a common substring */
  assert haveCommonKSubstringPred(0, str1, str2);
  return;
}