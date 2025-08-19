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
  /* code modified by LLM (iteration 3): fixed loop invariants and termination */
  res := false;
  
  if |sub| > |str| {
    return;
  }
  
  var i := 0;
  while i <= |str| - |sub| && !res
    decreases |str| - |sub| - i + 1
    invariant 0 <= i <= |str| - |sub| + 1
    invariant !res ==> forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..])
    invariant res ==> isSubstringPred(sub, str)
  {
    if isPrefixPred(sub, str[i..]) {
      res := true;
      /* code modified by LLM (iteration 3): added assertion to help prove postcondition */
      assert isSubstringPred(sub, str);
    } else {
      i := i + 1;
    }
  }
  
  /* code modified by LLM (iteration 3): added final assertion to prove postcondition */
  if !res {
    assert forall j :: 0 <= j <= |str| - |sub| ==> !isPrefixPred(sub, str[j..]);
    assert forall j :: 0 <= j <= |str| ==> !isPrefixPred(sub, str[j..]);
  }
}

//ATOM

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  /* code modified by LLM (iteration 1): removed assume statements and implemented proper logic */
  if |pre| > |str| {
    res := false;
  } else {
    res := (pre == str[..|pre|]);
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

//IMPL haveCommonKSubstring

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found <==> haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	/* code modified by LLM (iteration 4): fixed k=0 case and early returns */
	if k == 0 {
		found := true;
		return;
	}
	
	if |str1| < k {
		found := false;
		return;
	}
	
	found := false;
	var i := 0;
	/* code modified by LLM (iteration 4): fixed loop with proper invariants and corrected trigger syntax */
	while i <= |str1| - k && !found
		decreases |str1| - k - i + 1
		invariant 0 <= i <= |str1| - k + 1
		invariant !found ==> forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
		invariant found ==> haveCommonKSubstringPred(k, str1, str2)
	{
		var sub := str1[i..i+k];
		var isSubRes := isSubstring(sub, str2);
		
		if isSubRes {
			found := true;
			/* code modified by LLM (iteration 4): added witness for existential */
			assert haveCommonKSubstringPred(k, str1, str2);
		} else {
			/* code modified by LLM (iteration 4): added assertion to help maintain invariant */
			assert isNotSubstringPred(str1[i..i+k], str2);
		}
		
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 4): added final proof for !found case */
	if !found {
		assert forall i1 :: 0 <= i1 <= |str1| - k ==> isNotSubstringPred(str1[i1..i1+k], str2);
		/* code modified by LLM (iteration 4): prove negation of haveCommonKSubstringPred */
		assert forall i1, j1 :: 0 <= i1 <= |str1| - k && j1 == i1 + k ==> isNotSubstringPred(str1[i1..j1], str2);
		assert !haveCommonKSubstringPred(k, str1, str2);
	}
}