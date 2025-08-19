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

//IMPL isSubstring
method isSubstring(sub: string, str: string) returns (res:bool)
	ensures res <==> isSubstringPred(sub, str)
	ensures res ==> isSubstringPred(sub, str)
	// ensures !res ==> !isSubstringPred(sub, str)
	ensures isSubstringPred(sub, str) ==> res
	ensures isSubstringPred(sub, str) ==> res
	ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	/* code modified by LLM (iteration 1): Implement substring check using direct predicate evaluation instead of calling isPrefix */
	res := false;
	var i := 0;
	while i <= |str|
		invariant 0 <= i <= |str| + 1
		invariant !res ==> forall j :: 0 <= j < i ==> !isPrefixPred(sub, str[j..])
		invariant res ==> isSubstringPred(sub, str)
	{
		/* code modified by LLM (iteration 1): Check prefix condition directly */
		if |sub| <= |str[i..]| && sub == str[i..][..|sub|] {
			assert isPrefixPred(sub, str[i..]);
			assert isSubstringPred(sub, str);
			res := true;
			return;
		}
		i := i + 1;
	}
	/* code modified by LLM (iteration 1): Final assertions to establish postconditions */
	assert forall j :: 0 <= j <= |str| ==> !isPrefixPred(sub, str[j..]);
	assert isNotSubstringPred(sub, str);
}