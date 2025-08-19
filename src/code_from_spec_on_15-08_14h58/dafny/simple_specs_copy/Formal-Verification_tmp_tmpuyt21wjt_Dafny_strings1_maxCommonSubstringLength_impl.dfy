/* code modified by LLM (iteration 1): converted invalid syntax at beginning to proper Dafny comments */
// `maxCommonSubstringPredicate(str1, str2, len)` ensures that no common substring longer than `len` exists
// `haveCommonKSubstringPredicate(k, str1, str2)` checks if there's a common substring of length `k`
// I have a method `haveCommonKSubstring` that implements the predicate check

// The strategy is to find the largest `k` such that there exists a common substring of length `k`. I can do this by iterating from the maximum possible length down to 0.

//ATOM

predicate maxCommonSubstringPredicate(str1: string, str2: string, len:nat)
{
  forall k :: len < k <= |str1| ==> !haveCommonKSubstringPredicate(k, str1, str2)
}

//ATOM

predicate isSubstringPredicate (sub: string, str:string)
{
 |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}

//ATOM

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
  /* code modified by LLM (iteration 3): implemented actual substring check */
  if |sub| > |str| {
    res := false;
    return;
  }
  
  res := false;
  var i := 0;
  while i <= |str| - |sub|
    invariant 0 <= i <= |str| - |sub| + 1
    invariant !res ==> forall j :: 0 <= j < i ==> !isPrefixPredicate(sub, str[j..])
    invariant res ==> exists j :: 0 <= j < i && isPrefixPredicate(sub, str[j..])
  {
    var isMatch := isPrefix(sub, str[i..]);
    if isMatch {
      res := true;
      return;
    }
    i := i + 1;
  }
  return res;
}

//ATOM

method isPrefix(pre: string, str: string) returns (res: bool)
 ensures |pre| > |str| ==> !res
 ensures res == isPrefixPredicate(pre, str)
{
  /* code modified by LLM (iteration 3): implemented actual prefix check */
  if |pre| > |str| {
    res := false;
    return;
  }
  
  res := true;
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant res ==> forall j :: 0 <= j < i ==> pre[j] == str[j]
    invariant !res ==> exists j :: 0 <= j < i && pre[j] != str[j]
  {
    if pre[i] != str[i] {
      res := false;
      return;
    }
    i := i + 1;
  }
  return res;
}

//ATOM
predicate isPrefixPredicate(pre: string, str:string)
{
 |str| >= |pre| && pre <= str
}

//ATOM

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
 |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}

//ATOM

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
 ensures |str1| < k || |str2| < k ==> !found
 ensures haveCommonKSubstringPredicate(k,str1,str2) == found
{
  /* code modified by LLM (iteration 3): implemented actual common substring check */
  if |str1| < k || |str2| < k {
    found := false;
    return;
  }
  
  found := false;
  var i := 0;
  while i <= |str1| - k
    invariant 0 <= i <= |str1| - k + 1
    invariant !found ==> forall j :: 0 <= j < i ==> !isSubstringPredicate((str1[j..])[..k], str2)
    invariant found ==> exists j :: 0 <= j < i && isSubstringPredicate((str1[j..])[..k], str2)
  {
    var substring := (str1[i..])[..k];
    var isCommon := isSubstring(substring, str2);
    if isCommon {
      found := true;
      return;
    }
    i := i + 1;
  }
  return found;
}

//IMPL

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
ensures len <= |str1| && len <= |str2|
ensures len >= 0
ensures maxCommonSubstringPredicate(str1, str2, len)
{
  /* code modified by LLM (iteration 2): simplified implementation with better invariants */
  var maxLen := if |str1| <= |str2| then |str1| else |str2|;
  len := 0;
  
  var k := maxLen;
  while k > 0
    invariant 0 <= k <= maxLen
    invariant maxLen <= |str1| && maxLen <= |str2|
    invariant forall j :: k < j <= maxLen ==> !haveCommonKSubstringPredicate(j, str1, str2)
    invariant len == 0
    decreases k
  {
    var found := haveCommonKSubstring(k, str1, str2);
    if found {
      len := k;
      /* code modified by LLM (iteration 2): added lemma call to establish postcondition */
      assert haveCommonKSubstringPredicate(k, str1, str2);
      assert forall j :: k < j <= maxLen ==> !haveCommonKSubstringPredicate(j, str1, str2);
      establishMaxCommonSubstringPredicate(str1, str2, len, maxLen);
      return;
    }
    k := k - 1;
  }
  
  /* code modified by LLM (iteration 2): handle case when no substring found */
  assert k == 0;
  assert forall j :: 0 < j <= maxLen ==> !haveCommonKSubstringPredicate(j, str1, str2);
  establishMaxCommonSubstringPredicateZero(str1, str2, maxLen);
}

/* code modified by LLM (iteration 4): helper lemma to establish postcondition when len > 0 */
lemma establishMaxCommonSubstringPredicate(str1: string, str2: string, len: nat, maxLen: nat)
  requires len > 0
  requires maxLen <= |str1| && maxLen <= |str2|
  requires haveCommonKSubstringPredicate(len, str1, str2)
  requires forall j :: len < j <= maxLen ==> !haveCommonKSubstringPredicate(j, str1, str2)
  ensures maxCommonSubstringPredicate(str1, str2, len)
{
  /* code modified by LLM (iteration 4): proof that no substring longer than len exists */
  forall k | len < k <= |str1|
    ensures !haveCommonKSubstringPredicate(k, str1, str2)
  {
    if k <= maxLen {
      assert !haveCommonKSubstringPredicate(k, str1, str2);
    } else {
      /* code modified by LLM (iteration 4): fixed logic - if k > |str2|, then predicate is false */
      assert k > maxLen;
      if k > |str2| {
        // Since k > |str2|, no substring of length k can exist in str2
        assert !haveCommonKSubstringPredicate(k, str1, str2);
      } else {
        // k <= |str2| but k > maxLen, and maxLen = min(|str1|, |str2|)
        // Since maxLen <= |str1| and k > maxLen, we have k > maxLen
        // But maxLen = min(|str1|, |str2|), so if k <= |str2| then maxLen = |str1|
        // This means k > |str1|, which contradicts k <= |str1|
        assert false;
      }
    }
  }
}

/* code modified by LLM (iteration 4): helper lemma to establish postcondition when len = 0 */
lemma establishMaxCommonSubstringPredicateZero(str1: string, str2: string, maxLen: nat)
  requires maxLen <= |str1| && maxLen <= |str2|
  requires forall j :: 0 < j <= maxLen ==> !haveCommonKSubstringPredicate(j, str1, str2)
  ensures maxCommonSubstringPredicate(str1, str2, 0)
{
  /* code modified by LLM (iteration 4): proof that no positive-length substring exists */
  forall k | 0 < k <= |str1|
    ensures !haveCommonKSubstringPredicate(k, str1, str2)
  {
    if k <= maxLen {
      assert !haveCommonKSubstringPredicate(k, str1, str2);
    } else {
      /* code modified by LLM (iteration 4): fixed logic - if k > |str2|, then predicate is false */
      assert k > maxLen;
      if k > |str2| {
        // Since k > |str2|, no substring of length k can exist in str2
        assert !haveCommonKSubstringPredicate(k, str1, str2);
      } else {
        // k <= |str2| but k > maxLen, and maxLen = min(|str1|, |str2|)
        // Since maxLen <= |str1| and k > maxLen, we have k > maxLen
        // But maxLen = min(|str1|, |str2|), so if k <= |str2| then maxLen = |str1|
        // This means k > |str1|, which contradicts k <= |str1|
        assert false;
      }
    }
  }
}