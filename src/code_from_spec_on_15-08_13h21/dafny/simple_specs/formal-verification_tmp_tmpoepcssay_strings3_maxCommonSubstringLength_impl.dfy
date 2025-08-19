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
  assume {:axiom} res <==> isSubstringPred(sub, str);
  assume {:axiom} res ==> isSubstringPred(sub, str);
  assume {:axiom} isSubstringPred(sub, str) ==> res;
  assume {:axiom} isSubstringPred(sub, str) ==> res;
  assume {:axiom} !res <==> isNotSubstringPred(sub, str); // This postcondition follows from the above lemma.
}


//ATOM

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  res := false;
  assume {:axiom} !res <==> isNotPrefixPred(pre,str);
  assume {:axiom} res <==> isPrefixPred(pre,str);
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
  assume {:axiom} found <==> haveCommonKSubstringPred(k,str1,str2);
  assume {:axiom} !found <==> haveNotCommonKSubstringPred(k,str1,str2); // This postcondition follows from the above lemma.
}


//IMPL

/* code modified by LLM (iteration 1): added helper lemma to prove empty string is always a common substring */
lemma emptyStringIsCommonSubstring(str1: string, str2: string)
  ensures haveCommonKSubstringPred(0, str1, str2)
{
  /* code modified by LLM (iteration 1): provide proper proof that empty string is substring of any string */
  // The empty string str1[0..0] has length 0
  var emptyStr := str1[0..0];
  assert |emptyStr| == 0;
  
  // Empty string is a prefix of str2[0..] because |emptyStr| <= |str2[0..]| and emptyStr == str2[0..|emptyStr|]
  assert 0 <= |str2|;
  assert |emptyStr| <= |str2[0..]|;
  assert emptyStr == str2[0..0];
  assert emptyStr == str2[0..|emptyStr|];
  assert isPrefixPred(emptyStr, str2[0..]);
  
  // Therefore empty string is a substring of str2
  assert isSubstringPred(emptyStr, str2);
  
  // This satisfies the existential in haveCommonKSubstringPred for k=0
  assert 0 <= 0 <= |str1| - 0;
  assert 0 + 0 == 0;
  assert isSubstringPred(str1[0..0], str2);
}

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
  
  /* code modified by LLM (iteration 1): prove that empty string is always a common substring */
  emptyStringIsCommonSubstring(str1, str2);
}