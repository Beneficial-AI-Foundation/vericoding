// We spent 2h each on this assignment

// ATOM 
// We spent 2h each on this assignment

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
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
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
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	found := false;
	if k == 0 {
		found := true;
		return;
	}
	
	if |str1| < k {
		found := false;
		return;
	}
	
	var i1 := 0;
	while i1 <= |str1| - k
		invariant 0 <= i1 <= |str1| - k + 1
		invariant !found ==> (forall i :: 0 <= i < i1 ==> isNotSubstringPred(str1[i..i+k], str2))
		invariant found ==> haveCommonKSubstringPred(k, str1, str2)
	{
		var substring := str1[i1..i1+k];
		var isSubstr := isSubstring(substring, str2);
		if isSubstr {
			found := true;
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
	var k := |str1|;
	
	while k > 0
		invariant 0 <= k <= |str1|
		invariant (forall j :: k < j <= |str1| ==> !haveCommonKSubstringPred(j,str1,str2))
		decreases k
	{
		var hasCommon := haveCommonKSubstring(k, str1, str2);
		if hasCommon {
			len := k;
			return;
		}
		k := k - 1;
	}
	
	/* code modified by LLM (iteration 1): Set len to 0 and add assertion to help prove postcondition */
	len := 0;
	assert haveCommonKSubstringPred(0, str1, str2);
}