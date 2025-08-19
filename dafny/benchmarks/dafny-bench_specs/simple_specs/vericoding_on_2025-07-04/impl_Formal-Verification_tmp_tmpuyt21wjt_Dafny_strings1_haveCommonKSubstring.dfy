//ATOM

predicate isSubstringPredicate (sub: string, str:string)
{
 |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}


//ATOM

method isSubstring(sub: string, str: string) returns (res:bool)
ensures res == isSubstringPredicate(sub, str)
{
  res := false;
  assume res ==> isSubstringPredicate(sub, str);
  return res;
}


//ATOM

method isPrefix(pre: string, str: string) returns (res: bool)
 ensures |pre| > |str| ==> !res
 ensures res == isPrefixPredicate(pre, str)
{
  res := false;
  assume |pre| > |str| ==> !res;
  assume res ==> isPrefixPredicate(pre, str);
  return res;
}


//ATOM

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
 |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}


//ATOM
predicate isPrefixPredicate(pre: string, str:string)
{
 |str| >= |pre| && pre <= str
}


//IMPL haveCommonKSubstring

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
 ensures |str1| < k || |str2| < k ==> !found
 ensures haveCommonKSubstringPredicate(k,str1,str2) == found
{
    if |str1| < k || |str2| < k {
        found := false;
        return;
    }
    
    found := false;
    var i := 0;
    
    /* code modified by LLM (iteration 1): Fixed loop invariants to properly handle both found and not found cases */
    while i <= |str1| - k && !found
        invariant 0 <= i <= |str1| - k + 1
        invariant forall j :: 0 <= j < i ==> !isSubstringPredicate((str1[j..])[..k], str2)
        invariant found ==> (i > 0 && isSubstringPredicate((str1[i-1..])[..k], str2))
    {
        var substring := (str1[i..])[..k];
        var isSubstr := isSubstring(substring, str2);
        
        if isSubstr {
            found := true;
        } else {
            i := i + 1;
        }
    }
    
    /* code modified by LLM (iteration 1): Added proof logic to establish the postcondition */
    if found {
        // We found a common substring at position i-1
        assert i > 0;
        assert isSubstringPredicate((str1[i-1..])[..k], str2);
        assert 0 <= i-1 <= |str1| - k;
        assert haveCommonKSubstringPredicate(k, str1, str2);
    } else {
        // We checked all positions and found no common substring
        assert i > |str1| - k;
        assert forall j :: 0 <= j <= |str1| - k ==> !isSubstringPredicate((str1[j..])[..k], str2);
        assert !haveCommonKSubstringPredicate(k, str1, str2);
    }
}