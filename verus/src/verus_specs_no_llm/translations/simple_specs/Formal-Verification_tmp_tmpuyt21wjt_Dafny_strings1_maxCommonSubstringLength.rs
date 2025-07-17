// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn maxCommonSubstringPredicate(str1: String, str2: String, len: nat) -> bool {
    forall |k: int| len < k <= str1.len() ==> !haveCommonKSubstringPredicate(k, str1, str2)
}
spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() && (exists |i: int| 0 <= i <= str.len() && isPrefixPredicate(sub, str.index(i..)))
}
spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && pre <= str
}
spec fn haveCommonKSubstringPredicate(k: nat, str1: String, str2: String) -> bool {
    str1.len() >= k && str2.len() >= k && (exists |i: int| 0 <= i <= str1.len() - k && isSubstringPredicate((str1.index(i..))[..k], str2))
}

spec fn spec_isSubstring(sub: String, str: String) -> res:bool)
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
  found := false;
  assume |str1| < k || |str2| < k ==> !found;
  assume haveCommonKSubstringPredicate(k,str1,str2) ==> found;
  return found;
}


// SPEC

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat
    ensures
        res == isSubstringPredicate(sub, str),
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str),
        str1.len() < k | .len()str2| < k ==> !found,
        haveCommonKSubstringPredicate(k,str1,str2) == found,
        len <= str1.len() && len <= str2.len(),
        len >= 0,
        maxCommonSubstringPredicate(str1, str2, len)
;

proof fn lemma_isSubstring(sub: String, str: String) -> (res: bool)
ensures res == isSubstringPredicate(sub, str)
{
  res: = false;
  assume res ==> isSubstringPredicate(sub, str);
  return res;
}


//ATOM

method isPrefix(pre: String, str: string) returns (res: bool)
 ensures |pre| > |str| ==> !res
 ensures res == isPrefixPredicate(pre, str)
{
  res: = false;
  assume |pre| > |str| ==> !res;
  assume res ==> isPrefixPredicate(pre, str);
  return res;
}


//ATOM
predicate isPrefixPredicate(pre: String, str: string)
{
 |str| >= |pre| && pre <= str
}


//ATOM

predicate haveCommonKSubstringPredicate(k: nat, str1: String, str2: string)
{
 |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}


//ATOM


method haveCommonKSubstring(k: nat, str1: String, str2: string) returns (found: bool)
 ensures |str1| < k || |str2| < k ==> !found
 ensures haveCommonKSubstringPredicate(k, str1, str2) == found
{
  found: = false;
  assume |str1| < k || |str2| < k ==> !found;
  assume haveCommonKSubstringPredicate(k, str1, str2) ==> found;
  return found;
}


// SPEC

method maxCommonSubstringLength(str1: String, str2: string) returns (len:nat)
    ensures
        res == isSubstringPredicate(sub, str),
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str),
        str1.len() < k | .len()str2| < k ==> !found,
        haveCommonKSubstringPredicate(k,str1,str2) == found,
        len <= str1.len() && len <= str2.len(),
        len >= 0,
        maxCommonSubstringPredicate(str1, str2, len)
{
    (0, 0, String::new(), 0, 0, String::new(), 0, String::new(), 0, 0, String::new(), 0, 0, 0, 0, String::new(), 0)
}

}