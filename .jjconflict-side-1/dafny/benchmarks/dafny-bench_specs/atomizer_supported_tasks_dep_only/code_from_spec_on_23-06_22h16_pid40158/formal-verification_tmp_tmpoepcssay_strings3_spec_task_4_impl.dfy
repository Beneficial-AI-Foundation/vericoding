// ATOM 
predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}


// ATOM 

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}


//ATOM_PLACEHOLDER_PrefixNegationLemma

//IMPL isPrefix
method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
	if |pre| > |str| {
		res := false;
	} else {
		res := (pre == str[..|pre|]);
	}
}

// ATOM 
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}


// ATOM 

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}


//ATOM_PLACEHOLDER_SubstringNegationLemma

//IMPL isSubstring
method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	ensures  res ==> isSubstringPred(sub, str)
	// ensures  !res ==> !isSubstringPred(sub, str)
	ensures  isSubstringPred(sub, str) ==> res
	ensures  isSubstringPred(sub, str) ==> res
	ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	res := false;
	var i := 0;
	while i <= |str|
		invariant 0 <= i <= |str| + 1
		invariant !res ==> (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]))
		invariant res ==> isSubstringPred(sub, str)
	{
		var isPrefix := isPrefix(sub, str[i..]);
		if isPrefix {
			res := true;
			/* code modified by LLM (iteration 1): Add assertion to help verification */
			assert isPrefixPred(sub, str[i..]);
			assert isSubstringPred(sub, str);
			break;
		}
		i := i + 1;
	}
}




// ATOM 



predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}


// ATOM 

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}


//ATOM_PLACEHOLDER_commonKSubstringLemma

//IMPL haveCommonKSubstring
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	found := false;
	if k > |str1| {
		return;
	}
	
	var i1 := 0;
	while i1 <= |str1| - k
		invariant 0 <= i1 <= |str1| - k + 1
		invariant !found ==> (forall i :: 0 <= i < i1 ==> isNotSubstringPred(str1[i..i+k], str2))
		invariant found ==> haveCommonKSubstringPred(k, str1, str2)
	{
		var substr := str1[i1..i1+k];
		var isSubstr := isSubstring(substr, str2);
		if isSubstr {
			found := true;
			/* code modified by LLM (iteration 1): Add assertion to help verification */
			assert isSubstringPred(str1[i1..i1+k], str2);
			assert haveCommonKSubstringPred(k, str1, str2);
			break;
		}
		i1 := i1 + 1;
	}
}


//IMPL maxCommonSubstringLength
method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
	/* code modified by LLM (iteration 1): Handle empty string case properly */
	if |str1| == 0 {
		len := 0;
		assert haveCommonKSubstringPred(0, str1, str2);
		return;
	}
	
	/* code modified by LLM (iteration 1): Establish that empty string is always a common substring */
	assert str1[0..0] == "";
	assert "" == str2[0..0];
	assert isPrefixPred("", str2[0..]);
	assert isSubstringPred("", str2);
	assert 0 <= 0 <= |str1| - 0;
	assert haveCommonKSubstringPred(0, str1, str2);
	
	len := 0;
	var k := 1;
	
	/* code modified by LLM (iteration 1): Search from smallest to largest instead of largest to smallest */
	while k <= |str1|
		invariant 1 <= k <= |str1| + 1
		invariant haveCommonKSubstringPred(len, str1, str2)
		invariant len < k
		invariant forall j :: len < j < k ==> !haveCommonKSubstringPred(j, str1, str2)
	{
		var hasCommon := haveCommonKSubstring(k, str1, str2);
		if hasCommon {
			len := k;
		}
		k := k + 1;
	}
	
	/* code modified by LLM (iteration 1): Add final assertion to help prove postcondition */
	assert forall j :: len < j <= |str1| ==> !haveCommonKSubstringPred(j, str1, str2);
}