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


// ATOM 

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}


// IMPL isPrefix

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


// ATOM 

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


// IMPL isSubstring

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	ensures  res ==> isSubstringPred(sub, str)
	// ensures  !res ==> !isSubstringPred(sub, str)
	ensures  isSubstringPred(sub, str) ==> res
	ensures  isSubstringPred(sub, str) ==> res
	ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	if |sub| > |str| {
		res := false;
		return;
	}
	
	var i := 0;
	while i <= |str| - |sub|
		invariant 0 <= i <= |str| - |sub| + 1
		invariant forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
	{
		var prefixRes := isPrefix(sub, str[i..]);
		if prefixRes {
			res := true;
			return;
		}
		i := i + 1;
	}
	res := false;
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


// ATOM 

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}


// IMPL haveCommonKSubstring

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	if k > |str1| {
		found := false;
		return;
	}
	
	var i := 0;
	while i <= |str1| - k
		invariant 0 <= i <= |str1| - k + 1
		invariant forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
	{
		var substring := str1[i..i+k];
		var substringFound := isSubstring(substring, str2);
		if substringFound {
			found := true;
			return;
		}
		i := i + 1;
	}
	found := false;
}


// IMPL maxCommonSubstringLength

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
	/* code modified by LLM (iteration 1): Handle empty string case with proper proof */
	if |str1| == 0 {
		len := 0;
		// Need to prove haveCommonKSubstringPred(0,str1,str2) holds
		// For k=0, we need exists i1, j1 :: 0 <= i1 <= 0 && j1 == i1 + 0 && isSubstringPred(str1[i1..j1],str2)
		// This means i1=0, j1=0, and str1[0..0] == "" is a substring of str2
		assert str1[0..0] == "";
		assert |""| == 0;
		assert |""| <= |str2|;
		assert "" == str2[..0];
		assert isPrefixPred("", str2);
		assert isSubstringPred("", str2);
		return;
	}
	
	/* code modified by LLM (iteration 1): Search from longest to shortest substring */
	var k := |str1|;
	
	while k > 0
		invariant 0 <= k <= |str1|
		invariant forall j :: k < j <= |str1| ==> !haveCommonKSubstringPred(j,str1,str2)
	{
		var hasCommon := haveCommonKSubstring(k, str1, str2);
		if hasCommon {
			len := k;
			return;
		}
		k := k - 1;
	}
	
	/* code modified by LLM (iteration 1): Handle case when no positive-length substring found */
	len := 0;
	// Prove that haveCommonKSubstringPred(0,str1,str2) holds
	// Empty string is always a substring
	assert str1[0..0] == "";
	assert |""| <= |str2|;
	assert "" == str2[..0];
	assert isPrefixPred("", str2);
	assert isSubstringPred("", str2);
}