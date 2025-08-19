//ATOM
// We spent 2h each on this assignment

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
  assume {:axiom} res <==> isSubstringPred(sub, str);
  return res;
}


//ATOM

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  res := false;
  assume {:axiom} !res <==> isNotPrefixPred(pre,str);
  assume {:axiom} res <==> isPrefixPred(pre,str);
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
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
  found := false;
  assume {:axiom} found <==> haveCommonKSubstringPred(k,str1,str2);
  return found;
}


//IMPL maxCommonSubstringLength

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
    
    /* code modified by LLM (iteration 1): Added assertion to establish postcondition for len = 0 case */
    // When len = 0, we need to prove haveCommonKSubstringPred(0,str1,str2)
    // This means there exists a common substring of length 0, which is always true
    // since the empty string is always a substring of any string
    assert len == 0;
    assert haveCommonKSubstringPred(0,str1,str2) by {
        // The empty string str1[0..0] = "" is a substring of str2
        // We can witness i1=0, j1=0 for the existential in haveCommonKSubstringPred
        assert 0 <= 0 <= |str1| - 0; // 0 <= 0 <= |str1|, which is true
        assert isSubstringPred(str1[0..0], str2) by {
            // str1[0..0] is the empty string, which is a prefix of str2[0..]
            assert isPrefixPred("", str2[0..]) by {
                assert |""| <= |str2[0..]|; // 0 <= |str2|, always true
                assert "" == str2[0..][..0]; // "" == "", which is true
            }
        }
    }
}