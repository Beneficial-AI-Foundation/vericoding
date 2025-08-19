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
  /* code modified by LLM (iteration 1): Fixed bounds checking and loop invariants */
  if |sub| > |str| {
    res := false;
    return;
  }
  
  res := false;
  var i := 0;
  while i <= |str| - |sub| && !res
    invariant 0 <= i <= |str| - |sub| + 1
    invariant !res ==> forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..])
    invariant res ==> exists j :: 0 <= j < i && isPrefixPred(sub, str[j..])
  {
    if sub == str[i..i+|sub|] {
      res := true;
      /* code modified by LLM (iteration 1): Help prove postcondition */
      assert isPrefixPred(sub, str[i..]);
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Help prove postcondition */
  if res {
    assert exists j :: 0 <= j < i && isPrefixPred(sub, str[j..]);
    assert isSubstringPred(sub, str);
  } else {
    assert forall j :: 0 <= j <= |str| - |sub| ==> !isPrefixPred(sub, str[j..]);
    if |sub| == 0 {
      assert isPrefixPred(sub, str[0..]);
      assert isSubstringPred(sub, str);
      res := true;
    }
  }
  
  return res;
}


//ATOM

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  /* code modified by LLM (iteration 1): Removed assume statements and implemented proper logic */
  if |pre| > |str| {
    res := false;
  } else {
    res := (pre == str[..|pre|]);
  }
  return res;
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
	/* code modified by LLM (iteration 1): Handle edge cases properly */
	if k == 0 {
		found := true;
		assert 0 <= 0 <= |str1| - 0 && 0 == 0 + 0 && isSubstringPred(str1[0..0], str2);
		return;
	}
	
	if |str1| < k {
		found := false;
		assert forall i1, j1 :: 0 <= i1 <= |str1| - k && j1 == i1 + k ==> false;
		assert !haveCommonKSubstringPred(k, str1, str2);
		return;
	}
	
	found := false;
	var i := 0;
	
	/* code modified by LLM (iteration 1): Fixed loop with proper invariants and triggers */
	while i <= |str1| - k && !found
		invariant 0 <= i <= |str1| - k + 1
		invariant !found ==> forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2) by {
			if !found {
				forall i1 | 0 <= i1 < i
					ensures isNotSubstringPred(str1[i1..i1+k], str2)
				{}
			}
		}
		invariant found ==> haveCommonKSubstringPred(k, str1, str2)
		decreases |str1| - k - i + 1
	{
		var substring := str1[i..i+k];
		var isSubStr := isSubstring(substring, str2);
		
		if isSubStr {
			found := true;
			/* code modified by LLM (iteration 1): Prove postcondition when substring found */
			assert isSubstringPred(str1[i..i+k], str2);
			assert 0 <= i <= |str1| - k && (i + k) == i + k && isSubstringPred(str1[i..i+k], str2);
			assert haveCommonKSubstringPred(k, str1, str2);
		}
		
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 1): Prove postcondition when no substring found */
	if !found {
		/* code modified by LLM (iteration 1): Use explicit forall statement to help verification */
		forall i1, j1 | 0 <= i1 <= |str1| - k && j1 == i1 + k
			ensures isNotSubstringPred(str1[i1..j1], str2)
		{
			assert i1 < i || i1 == i;
			if i1 < i {
				assert isNotSubstringPred(str1[i1..i1+k], str2);
				assert str1[i1..j1] == str1[i1..i1+k];
			} else {
				assert i1 == i;
				assert i > |str1| - k;
				assert false;
			}
		}
		assert !haveCommonKSubstringPred(k, str1, str2);
	}
}