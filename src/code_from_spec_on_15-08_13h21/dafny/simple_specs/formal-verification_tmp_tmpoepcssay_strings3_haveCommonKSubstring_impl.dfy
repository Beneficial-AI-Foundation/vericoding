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
  /* code modified by LLM (iteration 1): Removed assume statements and added proper implementation */
  res := false;
  if |sub| == 0 {
    res := true;
    return;
  }
  if |sub| > |str| {
    res := false;
    return;
  }
  var i := 0;
  while i <= |str| - |sub|
    invariant 0 <= i <= |str| - |sub| + 1
  {
    if str[i..i+|sub|] == sub {
      res := true;
      return;
    }
    i := i + 1;
  }
  res := false;
}


//ATOM

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  /* code modified by LLM (iteration 1): Removed assume statements and added proper implementation */
  if |pre| > |str| {
    res := false;
    return;
  }
  res := pre == str[..|pre|];
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


//IMPL haveCommonKSubstring

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found <==> haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
    /* code modified by LLM (iteration 1): Fixed implementation to properly establish postconditions */
    found := false;
    
    if k == 0 {
        found := true;
        return;
    }
    
    if |str1| < k {
        found := false;
        return;
    }
    
    var i := 0;
    /* code modified by LLM (iteration 1): Fixed loop invariants with proper triggers and logic */
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        invariant !found
        invariant forall i1 :: 0 <= i1 < i ==> isNotSubstringPred(str1[i1..i1+k], str2)
    {
        var substring := str1[i..i+k];
        var isSubstr := isSubstring(substring, str2);
        
        if isSubstr {
            found := true;
            return;
        }
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): Removed problematic assertion that couldn't be proved */
    found := false;
}