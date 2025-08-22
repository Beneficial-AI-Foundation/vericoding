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
	/* code modified by LLM (iteration 1): simplified logic to directly implement the predicate definition */
	if |pre| <= |str| && pre == str[..|pre|] {
		res := true;
	} else {
		res := false;
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
	/* code modified by LLM (iteration 1): fixed loop condition and invariants for proper verification */
	while i <= |str|
		invariant 0 <= i <= |str| + 1
		invariant !res ==> forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
		invariant res ==> isSubstringPred(sub, str)
	{
		/* code modified by LLM (iteration 1): handle case when i == |str| to avoid out of bounds */
		if i == |str| {
			/* code modified by LLM (iteration 1): check if empty suffix can be a prefix */
			if |sub| == 0 {
				res := true;
				/* code modified by LLM (iteration 1): prove the postcondition */
				assert isPrefixPred(sub, str[i..]);
				assert exists j :: 0 <= j <= |str| && isPrefixPred(sub, str[j..]);
			}
			break;
		}
		
		var prefixResult := isPrefix(sub, str[i..]);
		if prefixResult {
			res := true;
			/* code modified by LLM (iteration 1): prove existential for postcondition */
			assert isPrefixPred(sub, str[i..]);
			assert exists j :: 0 <= j <= |str| && isPrefixPred(sub, str[j..]);
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
	/* code modified by LLM (iteration 1): handle edge cases properly */
	if k == 0 {
		found := true;
		/* code modified by LLM (iteration 1): prove that empty string is substring when k=0 */
		if |str1| > 0 {
			assert str1[0..0] == "";
			assert isPrefixPred("", str2[0..]);
			assert isSubstringPred("", str2);
			assert 0 <= 0 <= |str1| - 0 && 0 == 0 + 0;
			assert exists i1, j1 :: 0 <= i1 <= |str1| - k && j1 == i1 + k && isSubstringPred(str1[i1..j1], str2);
		}
		return;
	}
	
	if |str1| < k {
		found := false;
		/* code modified by LLM (iteration 1): prove no valid substring exists when str1 too short */
		assert forall i1, j1 :: 0 <= i1 <= |str1| - k && j1 == i1 + k ==> false;
		return;
	}
	
	found := false;
	var i := 0;
	/* code modified by LLM (iteration 1): corrected loop bounds and invariants */
	while i <= |str1| - k
		invariant 0 <= i <= |str1| - k + 1
		invariant !found ==> forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
		invariant found ==> haveCommonKSubstringPred(k, str1, str2)
	{
		var substring := str1[i..i+k];
		var substringResult := isSubstring(substring, str2);
		if substringResult {
			found := true;
			/* code modified by LLM (iteration 1): prove the existential quantifier */
			assert isSubstringPred(str1[i..i+k], str2);
			assert 0 <= i <= |str1| - k && i + k == i + k;
			assert exists i1, j1 :: 0 <= i1 <= |str1| - k && j1 == i1 + k && isSubstringPred(str1[i1..j1], str2);
			break;
		}
		i := i + 1;
	}
}


//ATOM_PLACEHOLDER_maxCommonSubstringLength