//ATOM
// We spent 2h each on this assignment

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
  assume res <==> isSubstringPred(sub, str);
  return res;
}


//ATOM

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  res := false;
  assume !res <==> isNotPrefixPred(pre,str);
  assume res <==> isPrefixPred(pre,str);
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
	/* code modified by LLM (iteration 1): Handle edge case when k=0 */
	if k == 0 {
		found := true;
		return;
	}
	
	/* code modified by LLM (iteration 1): Handle case when str1 is too short */
	if |str1| < k {
		found := false;
		return;
	}
	
	found := false;
	var i := 0;
	
	/* code modified by LLM (iteration 1): Fixed loop with corrected invariants and bounds */
	while i <= |str1| - k
		invariant 0 <= i <= |str1| - k + 1
		invariant found ==> haveCommonKSubstringPred(k, str1, str2)
		invariant !found ==> forall i1 :: 0 <= i1 < i && i1 <= |str1| - k ==> !isSubstringPred(str1[i1..i1+k], str2)
		decreases |str1| - k + 1 - i
	{
		var substring := str1[i..i+k];
		var isSubstr := isSubstring(substring, str2);
		
		if isSubstr {
			/* code modified by LLM (iteration 1): Added assertion to help prove postcondition */
			assert isSubstringPred(substring, str2);
			assert substring == str1[i..i+k];
			assert 0 <= i <= |str1| - k && i + k == i + k;
			assert haveCommonKSubstringPred(k, str1, str2);
			found := true;
			return;
		}
		
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 1): Added final assertion to help prove postcondition when not found */
	assert forall i1 :: 0 <= i1 <= |str1| - k ==> !isSubstringPred(str1[i1..i1+k], str2);
	assert !haveCommonKSubstringPred(k, str1, str2);
}