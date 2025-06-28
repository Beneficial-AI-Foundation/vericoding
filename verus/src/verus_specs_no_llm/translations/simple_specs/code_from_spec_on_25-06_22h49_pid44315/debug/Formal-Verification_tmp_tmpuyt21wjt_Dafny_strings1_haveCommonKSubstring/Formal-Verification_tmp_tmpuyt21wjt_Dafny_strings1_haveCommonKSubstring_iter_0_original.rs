// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() && (exists i :: 0 <= i <= str.len() && isPrefixPredicate(sub, str.spec_index(i..)))
}
spec fn haveCommonKSubstringPredicate(k: nat, str1: String, str2: String) -> bool {
    str1.len() >= k && str2.len() >= k && (exists i :: 0 <= i <= str1.len() - k && isSubstringPredicate((str1.spec_index(i..))[..k], str2))
}
spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && pre <= str
}

fn isSubstring(sub: String, str: String) -> (res: bool)
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

predicate haveCommonKSubstringPredicate(k: nat, str1: String, str2: string)
{
 |str1| >= k && |str2| >= k && (exists i :: 0 <= i <= |str1| - k && isSubstringPredicate((str1[i..])[..k], str2))
}


//ATOM
predicate isPrefixPredicate(pre: String, str: string)
{
 |str| >= |pre| && pre <= str
}


// SPEC


method haveCommonKSubstring(k: nat, str1: String, str2: string) returns (found: bool)
    ensures
        res == isSubstringPredicate(sub, str),
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str),
        str1.len() < k | .len()str2| < k ==> !found,
        haveCommonKSubstringPredicate(k,str1,str2) == found
{
    return (0, 0, String::new(), 0, 0, 0, String::new(), 0, String::new(), 0, String::new(), 0);
}

}