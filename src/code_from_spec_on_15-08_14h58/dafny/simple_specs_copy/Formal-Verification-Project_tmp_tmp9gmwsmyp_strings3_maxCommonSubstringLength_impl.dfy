//ATOM
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

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
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

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found <==> haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
  found := false;
  assume found <==> haveCommonKSubstringPred(k,str1,str2);
  return found;
}


//IMPL

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
    len := |str1|;
    
    while len > 0
        invariant 0 <= len <= |str1|
        invariant forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2)
    {
        var found := haveCommonKSubstring(len, str1, str2);
        if found {
            return;
        }
        len := len - 1;
    }
    
    /* code modified by LLM (iteration 1): establish postcondition for len = 0 case */
    // At this point len == 0
    // We need to prove haveCommonKSubstringPred(0, str1, str2)
    // This follows from the fact that the empty string is always a common substring
    var emptyFound := haveCommonKSubstring(0, str1, str2);
    assert emptyFound; // This should be true as empty string is always a common substring
    
    return;
}