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
  /* code modified by LLM (iteration 1): implement basic substring check */
  res := false;
  var i := 0;
  while i <= |str|
    invariant 0 <= i <= |str| + 1
    invariant !res ==> forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..])
    invariant res ==> isSubstringPred(sub, str)
  {
    if i <= |str| && isPrefixPred(sub, str[i..]) {
      res := true;
      return;
    }
    i := i + 1;
  }
  return res;
}


//ATOM

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  /* code modified by LLM (iteration 1): implement basic prefix check */
  if |pre| > |str| {
    res := false;
    return;
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

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

/* code modified by LLM (iteration 1): helper lemma for empty string substring property */
lemma EmptyStringIsSubstring(str: string)
  ensures isSubstringPred("", str)
{
  assert isPrefixPred("", str[0..]);
  assert 0 <= 0 <= |str|;
}

//IMPL haveCommonKSubstring

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found <==> haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	/* code modified by LLM (iteration 2): handle k=0 case properly */
	if k == 0 {
		found := true;
		EmptyStringIsSubstring(str2);
		assert haveCommonKSubstringPred(k, str1, str2) by {
			assert isSubstringPred("", str2);
			assert 0 <= 0 <= |str1| - 0 && 0 == 0 + 0;
			assert str1[0..0] == "";
		}
		return;
	}
	
	/* code modified by LLM (iteration 2): handle case where str1 is too short */
	if |str1| < k {
		found := false;
		return;
	}
	
	found := false;
	var i := 0;
	while i <= |str1| - k
		invariant 0 <= i <= |str1| - k + 1
		/* code modified by LLM (iteration 2): fixed loop invariant with proper trigger and logic */
		invariant !found ==> forall i1 {:trigger str1[i1..i1+k]} :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
		invariant found ==> haveCommonKSubstringPred(k, str1, str2)
	{
		var substring := str1[i..i+k];
		var isSubstr := isSubstring(substring, str2);
		
		if isSubstr {
			/* code modified by LLM (iteration 2): establish postcondition when substring found */
			found := true;
			assert haveCommonKSubstringPred(k, str1, str2) by {
				assert isSubstringPred(str1[i..i+k], str2);
				assert 0 <= i <= |str1| - k && (i + k) == i + k;
			}
			return;
		}
		
		/* code modified by LLM (iteration 2): establish that current substring is not in str2 */
		assert !isSubstringPred(str1[i..i+k], str2);
		assert isNotSubstringPred(str1[i..i+k], str2) by {
			assert forall j :: 0 <= j <= |str2| ==> !isPrefixPred(str1[i..i+k], str2[j..]);
		}
		
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 2): establish postcondition when no substring found */
	assert !haveCommonKSubstringPred(k, str1, str2) by {
		/* code modified by LLM (iteration 2): prove all substrings have been checked and found to not be in str2 */
		assert forall i1 :: 0 <= i1 <= |str1| - k ==> isNotSubstringPred(str1[i1..i1+k], str2);
		assert forall i1, j1 :: 0 <= i1 <= |str1| - k && j1 == i1 + k ==> !isSubstringPred(str1[i1..j1], str2);
	}
}