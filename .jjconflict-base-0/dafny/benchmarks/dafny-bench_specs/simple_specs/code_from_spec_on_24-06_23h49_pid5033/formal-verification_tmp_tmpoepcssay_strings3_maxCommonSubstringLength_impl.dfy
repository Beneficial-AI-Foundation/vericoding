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
	ensures res ==> isSubstringPred(sub, str)
	// ensures !res ==> !isSubstringPred(sub, str)
	ensures isSubstringPred(sub, str) ==> res
	ensures isSubstringPred(sub, str) ==> res
	ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
  res := false;
  assume res <==> isSubstringPred(sub, str);
  assume res ==> isSubstringPred(sub, str);
  assume isSubstringPred(sub, str) ==> res;
  assume isSubstringPred(sub, str) ==> res;
  assume !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.;
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


//ATOM

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found <==> haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
  found := false;
  assume found <==> haveCommonKSubstringPred(k,str1,str2);
  assume !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.;
  return found;
}


//IMPL maxCommonSubstringLength

/* code modified by LLM (iteration 1): Added helper lemma to prove empty string property */
lemma EmptyStringIsCommonSubstring(str1: string, str2: string)
    ensures haveCommonKSubstringPred(0, str1, str2)
{
    // For k=0, the empty string str1[0..0] is always a substring of str2
    assert isPrefixPred("", str2[0..]);
    assert isSubstringPred("", str2);
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
    /* code modified by LLM (iteration 1): Corrected loop structure and invariants */
    var k := |str1|;
    
    while k >= 0
        invariant 0 <= k <= |str1|
        invariant forall j :: k < j <= |str1| ==> !haveCommonKSubstringPred(j,str1,str2)
        decreases k
    {
        var found := haveCommonKSubstring(k, str1, str2);
        if found {
            len := k;
            return;
        }
        
        if k == 0 {
            break;
        }
        k := k - 1;
    }
    
    /* code modified by LLM (iteration 1): Handle the case where no common substring found except empty string */
    len := 0;
    EmptyStringIsCommonSubstring(str1, str2);
}