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


//IMPL isSubstring

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
    var i := 0;
    res := false;
    
    /* code modified by LLM (iteration 1): implement prefix check directly to avoid assume statements */
    while i <= |str|
        invariant 0 <= i <= |str| + 1
        invariant res ==> isSubstringPred(sub, str)
        invariant !res ==> forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..])
    {
        /* code modified by LLM (iteration 1): direct implementation of prefix check */
        var isPrefixMatch := true;
        if |sub| > |str| - i {
            isPrefixMatch := false;
        } else {
            var k := 0;
            while k < |sub|
                invariant 0 <= k <= |sub|
                invariant isPrefixMatch ==> forall m :: 0 <= m < k ==> sub[m] == str[i + m]
            {
                if sub[k] != str[i + k] {
                    isPrefixMatch := false;
                    break;
                }
                k := k + 1;
            }
        }
        
        if isPrefixMatch {
            /* code modified by LLM (iteration 1): prove that we found a substring match */
            assert |sub| <= |str| - i;
            assert forall m :: 0 <= m < |sub| ==> sub[m] == str[i + m];
            assert sub == str[i..i + |sub|];
            assert isPrefixPred(sub, str[i..]);
            assert isSubstringPred(sub, str);
            res := true;
            return;
        }
        
        /* code modified by LLM (iteration 1): prove that prefix doesn't match at position i */
        assert !isPrefixPred(sub, str[i..]);
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): prove that no substring was found */
    assert forall j :: 0 <= j <= |str| ==> !isPrefixPred(sub, str[j..]);
    assert !isSubstringPred(sub, str);
}