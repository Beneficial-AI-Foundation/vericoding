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


// ATOM 

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


//IMPL isSubstring

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	res := false;
	var i := 0;
	while i <= |str|
		invariant 0 <= i <= |str| + 1
		invariant !res ==> (forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..]))
		invariant res ==> isSubstringPred(sub, str)
	{
		var prefixResult := isPrefix(sub, str[i..]);
		if prefixResult {
			res := true;
			return;
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


// ATOM 

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}


//IMPL haveCommonKSubstring

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	found := false;
	if k > |str1| {
		return;
	}
	
	var i1 := 0;
	while i1 <= |str1| - k
		invariant 0 <= i1 <= |str1| - k + 1
		invariant !found ==> (forall i :: 0 <= i < i1 ==> !isSubstringPred(str1[i..i+k], str2))
		invariant found ==> haveCommonKSubstringPred(k, str1, str2)
	{
		var substring := str1[i1..i1+k];
		var substringResult := isSubstring(substring, str2);
		if substringResult {
			found := true;
			return;
		}
		i1 := i1 + 1;
	}
}


// ATOM 

lemma haveCommon0SubstringLemma(str1:string, str2:string)
    ensures  haveCommonKSubstringPred(0,str1,str2)
{
}


//IMPL maxCommonSubstringLength

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
	/* code modified by LLM (iteration 1): initialize len to 0 and establish base case */
	len := 0;
	haveCommon0SubstringLemma(str1, str2);
	
	var k := 1;
	
	/* code modified by LLM (iteration 1): iterate from 1 to |str1| to find maximum k with common substring */
	while k <= |str1|
		invariant 1 <= k <= |str1| + 1
		invariant haveCommonKSubstringPred(len, str1, str2)
		invariant forall j :: len < j < k ==> !haveCommonKSubstringPred(j, str1, str2)
		invariant len < k
	{
		var hasCommon := haveCommonKSubstring(k, str1, str2);
		if hasCommon {
			/* code modified by LLM (iteration 1): update len when we find a common k-substring */
			len := k;
		}
		k := k + 1;
	}
}