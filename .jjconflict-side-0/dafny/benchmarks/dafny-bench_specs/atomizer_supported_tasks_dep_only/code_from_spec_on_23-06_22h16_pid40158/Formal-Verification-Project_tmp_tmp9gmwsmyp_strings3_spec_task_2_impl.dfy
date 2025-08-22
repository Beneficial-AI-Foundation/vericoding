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
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	res := false;
	var i := 0;
	while i <= |str|
		invariant 0 <= i <= |str| + 1
		invariant !res ==> forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
		invariant res ==> exists j :: 0 <= j < i && isPrefixPred(sub, str[j..])
	{
		var prefixResult := isPrefix(sub, str[i..]);
		if prefixResult {
			res := true;
			break;
		}
		i := i + 1;
	}
}



//ATOM_PLACEHOLDER_haveCommonKSubstringPred

//ATOM_PLACEHOLDER_haveNotCommonKSubstringPred

//ATOM_PLACEHOLDER_commonKSubstringLemma

//ATOM_PLACEHOLDER_haveCommonKSubstring

//ATOM_PLACEHOLDER_haveCommon0SubstringLemma

//ATOM_PLACEHOLDER_maxCommonSubstringLength