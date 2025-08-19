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
    
    /* code modified by LLM (iteration 1): Updated loop to properly establish the postcondition without relying on ATOM method calls */
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        invariant found ==> (exists j :: 0 <= j < i && isSubstringPredicate((str1[j..])[..k], str2))
        invariant !found ==> (forall j :: 0 <= j < i ==> !isSubstringPredicate((str1[j..])[..k], str2))
    {
        var substring := (str1[i..])[..k];
        
        /* code modified by LLM (iteration 1): Implement substring check directly instead of calling ATOM method */
        var substringFound := false;
        var j := 0;
        while j <= |str2| - |substring|
            invariant 0 <= j <= |str2| - |substring| + 1
            invariant substringFound ==> (exists pos :: 0 <= pos < j && isPrefixPredicate(substring, str2[pos..]))
            invariant !substringFound ==> (forall pos :: 0 <= pos < j ==> !isPrefixPredicate(substring, str2[pos..]))
        {
            /* code modified by LLM (iteration 1): Check if substring is a prefix at position j */
            if j + |substring| <= |str2| && substring <= str2[j..] {
                substringFound := true;
                break;
            }
            j := j + 1;
        }
        
        if substringFound {
            found := true;
            /* code modified by LLM (iteration 1): Establish that we found the required substring */
            assert isSubstringPredicate((str1[i..])[..k], str2);
            return;
        }
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): When loop completes, establish that no common k-substring exists */
    assert forall j :: 0 <= j <= |str1| - k ==> !isSubstringPredicate((str1[j..])[..k], str2);
}