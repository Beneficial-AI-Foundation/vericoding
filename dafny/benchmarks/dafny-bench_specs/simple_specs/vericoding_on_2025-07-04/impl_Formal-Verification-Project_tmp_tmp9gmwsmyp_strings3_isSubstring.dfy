//ATOM
predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}


//ATOM
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| && isPrefixPred(sub, str[i..]))
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


//IMPL 

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
    var i := 0;
    while i <= |str|
        /* code modified by LLM (iteration 1): fixed loop invariant bound and added invariant to track substring property */
        invariant 0 <= i <= |str| + 1
        invariant forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
    {
        var prefixResult := isPrefix(sub, str[i..]);
        if prefixResult {
            /* code modified by LLM (iteration 1): added assertion to help prove postcondition when prefix is found */
            assert isPrefixPred(sub, str[i..]);
            assert isSubstringPred(sub, str);
            res := true;
            return;
        }
        /* code modified by LLM (iteration 1): added assertion to maintain loop invariant */
        assert isNotPrefixPred(sub, str[i..]);
        i := i + 1;
    }
    /* code modified by LLM (iteration 1): added assertion to prove postcondition when no prefix found */
    assert forall j :: 0 <= j <= |str| ==> isNotPrefixPred(sub, str[j..]);
    assert isNotSubstringPred(sub, str);
    assert !isSubstringPred(sub, str);
    res := false;
}