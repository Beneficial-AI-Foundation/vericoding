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
    /* code modified by LLM (iteration 1): fixed loop implementation and invariants */
    var i := 0;
    while i <= |str|
        invariant 0 <= i <= |str| + 1
        invariant forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..])
    {
        if i <= |str| {
            var prefixResult := isPrefix(sub, str[i..]);
            if prefixResult {
                res := true;
                return;
            }
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 1): set result to false when no substring found */
    res := false;
}