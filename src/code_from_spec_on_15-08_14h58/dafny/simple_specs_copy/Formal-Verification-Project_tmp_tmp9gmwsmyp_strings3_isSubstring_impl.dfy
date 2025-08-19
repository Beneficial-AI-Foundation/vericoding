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


//IMPL isPrefix

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  /* code modified by LLM (iteration 1): replaced assume statements with proper implementation */
  if |pre| > |str| {
    res := false;
    return;
  }
  
  res := true;
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant res ==> (forall j :: 0 <= j < i ==> pre[j] == str[j])
    invariant !res ==> (exists j :: 0 <= j < i && pre[j] != str[j])
    decreases |pre| - i
  {
    if pre[i] != str[i] {
      res := false;
      return;
    }
    i := i + 1;
  }
  
  assert res ==> (|pre| <= |str| && pre == str[..|pre|]);
  assert res ==> isPrefixPred(pre, str);
  assert !res ==> isNotPrefixPred(pre, str);
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
	/* code modified by LLM (iteration 2): fixed loop bounds and strengthened invariants */
	var i := 0;
	res := false;
	
	while i <= |str|
		invariant 0 <= i <= |str| + 1
		invariant res ==> isSubstringPred(sub, str)
		invariant !res ==> forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
		decreases |str| + 1 - i
	{
		var isP := isPrefix(sub, str[i..]);
		if isP {
			res := true;
			/* code modified by LLM (iteration 2): added assertion to establish substring property */
			assert isPrefixPred(sub, str[i..]);
			assert isSubstringPred(sub, str);
			return;
		}
		/* code modified by LLM (iteration 2): added assertion to maintain loop invariant */
		assert isNotPrefixPred(sub, str[i..]);
		i := i + 1;
	}
	
	/* code modified by LLM (iteration 2): strengthened final reasoning */
	assert i == |str| + 1;
	assert forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..]);
	assert forall j :: 0 <= j <= |str| ==> isNotPrefixPred(sub, str[j..]);
	assert !isSubstringPred(sub, str);
}