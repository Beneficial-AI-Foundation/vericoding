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

//IMPL 
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

//IMPL 
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
		invariant !res ==> forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
		invariant res ==> exists j :: 0 <= j < i && isPrefixPred(sub, str[j..])
	{
		var prefixRes := isPrefix(sub, str[i..]);
		if prefixRes {
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

//IMPL 
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	/* code modified by LLM (iteration 1): handle edge case for k=0 */
	if k == 0 {
		found := true;
		return;
	}
	
	/* code modified by LLM (iteration 1): handle case when str1 is too short */
	if |str1| < k {
		found := false;
		return;
	}
	
	found := false;
	var i := 0;
	/* code modified by LLM (iteration 1): fix loop bounds and invariants to match predicate definition */
	while i <= |str1| - k
		invariant 0 <= i <= |str1| - k + 1
		invariant !found ==> forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
		invariant found ==> exists i1 :: 0 <= i1 < i && isSubstringPred(str1[i1..i1+k], str2)
	{
		/* code modified by LLM (iteration 1): ensure substring extraction is correct */
		var substring := str1[i..i+k];
		var substringFound := isSubstring(substring, str2);
		if substringFound {
			found := true;
			break;
		}
		i := i + 1;
	}
}

//ATOM_PLACEHOLDER_maxCommonSubstringLength