// <vc-preamble>
predicate isPrefixPred(pre:string, str:string)
{
    (|pre| <= |str|) && 
    pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
    (|pre| > |str|) || 
    pre != str[..|pre|]
}

method isPrefix(pre: string, str: string) returns (res:bool)
    ensures !res <==> isNotPrefixPred(pre,str)
    ensures  res <==> isPrefixPred(pre,str)
{
  assume{:axiom} false;
}
predicate isSubstringPred(sub:string, str:string)
{
    (exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
    (forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [no change to logic, helper is correct] */
lemma SubstringProperties(sub: string, str: string)
  ensures forall j :: 0 <= j <= |str| && j > |str| - |sub| ==> isNotPrefixPred(sub, str[j..])
{
  forall j | 0 <= j <= |str| && j > |str| - |sub|
    ensures isNotPrefixPred(sub, str[j..])
  {
    assert |sub| > |str[j..]|;
  }
}
// </vc-helpers>

// <vc-spec>
method isSubstring(sub: string, str: string) returns (res:bool)
    ensures  res <==> isSubstringPred(sub, str)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): [Added guard for |sub| > |str| to fix loop invariant entry condition] */
{
  if |sub| > |str| {
    res := false;
    return;
  }

  res := false;
  var i := 0;
  while i <= |str| - |sub|
    invariant 0 <= i <= |str| - |sub| + 1
    invariant !res ==> forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
  {
    var is_prefix := isPrefix(sub, str[i..]);
    if is_prefix {
        res := true;
        return;
    }
    i := i + 1;
  }
  SubstringProperties(sub, str);
}
// </vc-code>
