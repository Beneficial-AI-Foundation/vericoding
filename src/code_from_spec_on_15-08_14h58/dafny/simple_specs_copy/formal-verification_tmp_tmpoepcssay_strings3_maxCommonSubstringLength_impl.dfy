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
	ensures res ==> isSubstringPred(sub, str)
	// ensures !res ==> !isSubstringPred(sub, str)
	ensures isSubstringPred(sub, str) ==> res
	ensures isSubstringPred(sub, str) ==> res
	ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
  /* code modified by LLM (iteration 1): Remove assume statements and implement proper logic */
  res := false;
  var i := 0;
  while i <= |str|
    invariant 0 <= i <= |str| + 1
    invariant !res ==> forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..])
  {
    if isPrefixCheck(sub, str[i..]) {
      res := true;
      return;
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 1): Helper method to check prefix */
method isPrefixCheck(pre: string, str: string) returns (result: bool)
  ensures result <==> isPrefixPred(pre, str)
{
  if |pre| > |str| {
    result := false;
  } else {
    result := pre == str[..|pre|];
  }
}

//ATOM

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  /* code modified by LLM (iteration 1): Remove assume statements and implement proper logic */
  if |pre| > |str| {
    res := false;
  } else {
    res := pre == str[..|pre|];
  }
}

//ATOM

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}

//ATOM

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

//ATOM

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found <==> haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
  /* code modified by LLM (iteration 1): Remove assume statements and implement proper logic */
  found := false;
  if k > |str1| {
    found := false;
    return;
  }
  
  var i1 := 0;
  while i1 <= |str1| - k
    invariant 0 <= i1 <= |str1| - k + 1
    invariant !found ==> forall j :: 0 <= j < i1 ==> !isSubstringPred(str1[j..j+k], str2)
  {
    var substr := str1[i1..i1+k];
    var isSubstr := isSubstring(substr, str2);
    if isSubstr {
      found := true;
      return;
    }
    i1 := i1 + 1;
  }
}

//IMPL 

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
    /* code modified by LLM (iteration 1): Handle special case when str1 is empty */
    if |str1| == 0 {
        len := 0;
        // Need to prove haveCommonKSubstringPred(0,str1,str2)
        // For k=0 and empty str1: exists i1, j1 :: 0 <= i1 <= 0-0 && j1 == i1 + 0 && isSubstringPred(str1[i1..j1],str2)
        // Take i1=0, j1=0: 0 <= 0 <= 0 && 0 == 0 + 0 && isSubstringPred("",str2)
        // Empty string is always a substring of any string
        assert 0 <= 0 <= |str1| - 0;
        assert 0 == 0 + 0;
        assert str1[0..0] == "";
        assert isPrefixPred("", str2[0..]);
        assert isSubstringPred("", str2);
        assert haveCommonKSubstringPred(0, str1, str2);
        return;
    }
    
    len := 0;
    var k := |str1|;
    
    /* code modified by LLM (iteration 1): Search from largest to smallest substring length */
    while k > 0
        invariant 0 <= k <= |str1|
        invariant forall j :: k < j <= |str1| ==> !haveCommonKSubstringPred(j,str1,str2)
    {
        var found := haveCommonKSubstring(k, str1, str2);
        if found {
            len := k;
            return;
        }
        k := k - 1;
    }
    
    /* code modified by LLM (iteration 1): At this point k = 0, prove empty string is common substring */
    len := 0;
    
    // For k=0: exists i1, j1 :: 0 <= i1 <= |str1|-0 && j1 == i1 + 0 && isSubstringPred(str1[i1..j1],str2)
    // Taking i1=0, j1=0: str1[0..0] = "" and empty string is always a substring
    assert 0 <= 0 <= |str1| - 0;
    assert 0 == 0 + 0;
    assert str1[0..0] == "";
    assert isPrefixPred("", str2[0..]);
    assert isSubstringPred("", str2);
    assert isSubstringPred(str1[0..0], str2);
    assert haveCommonKSubstringPred(0, str1, str2);
}