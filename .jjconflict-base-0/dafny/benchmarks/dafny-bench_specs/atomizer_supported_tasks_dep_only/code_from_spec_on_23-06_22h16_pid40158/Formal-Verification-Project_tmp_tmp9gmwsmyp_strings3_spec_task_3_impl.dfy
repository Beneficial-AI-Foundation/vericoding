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
    /* code modified by LLM (iteration 1): Fixed logic to properly handle both conditions */
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
    while i <= |str|
        invariant 0 <= i <= |str| + 1
        invariant res ==> isSubstringPred(sub, str)
        invariant !res ==> forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
    {
        /* code modified by LLM (iteration 1): Use isPrefix method and add assertion for verification */
        var prefixResult := isPrefix(sub, str[i..]);
        if prefixResult {
            /* code modified by LLM (iteration 1): Add assertion to help prove postcondition */
            assert isPrefixPred(sub, str[i..]);
            res := true;
            return;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 1): Add assertion to establish postcondition when loop completes */
    assert forall j :: 0 <= j <= |str| ==> isNotPrefixPred(sub, str[j..]);
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
    /* code modified by LLM (iteration 1): Handle edge cases properly */
    if |str1| < k {
        return;
    }
    
    /* code modified by LLM (iteration 1): Special handling for k=0 case */
    if k == 0 {
        var emptyIsSubstr := isSubstring("", str2);
        if emptyIsSubstr {
            /* code modified by LLM (iteration 1): Assert witness for k=0 case */
            assert str1[0..0] == "";
            assert isSubstringPred(str1[0..0], str2);
            assert haveCommonKSubstringPred(k, str1, str2);
            found := true;
        }
        return;
    }
    
    var i1 := 0;
    while i1 <= |str1| - k
        invariant 0 <= i1 <= |str1| - k + 1
        invariant found ==> haveCommonKSubstringPred(k, str1, str2)
        invariant !found ==> forall idx :: 0 <= idx < i1 ==> isNotSubstringPred(str1[idx..idx+k], str2)
    {
        var substr := str1[i1..i1+k];
        var isSubstr := isSubstring(substr, str2);
        if isSubstr {
            /* code modified by LLM (iteration 1): Add assertion to help prove postcondition */
            assert isSubstringPred(str1[i1..i1+k], str2);
            assert haveCommonKSubstringPred(k, str1, str2);
            found := true;
            return;
        }
        i1 := i1 + 1;
    }
}


//ATOM_PLACEHOLDER_haveCommon0SubstringLemma

//ATOM_PLACEHOLDER_maxCommonSubstringLength