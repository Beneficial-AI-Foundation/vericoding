// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() && (exists i :: 0 <= i <= str.len() && isPrefixPredicate(sub, str.spec_index(i..)))
}
spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && pre <= str
}

fn isPrefix(pre: String, str: String) -> (res: bool)
 ensures |pre| > |str| ==> !res
 ensures res == isPrefixPredicate(pre, str)
{
  res: = false;
  assume |pre| > |str| ==> !res;
  assume res ==> isPrefixPredicate(pre, str);
  return res;
}


//ATOM

predicate isSubstringPredicate (sub: String, str: string)
{
 |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}


//ATOM
predicate isPrefixPredicate(pre: String, str: string)
{
 |str| >= |pre| && pre <= str
}


// SPEC

method isSubstring(sub: string, str: string) returns (res:bool)
    ensures
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str),
        res == isSubstringPredicate(sub, str)
{
    return (0, 0, String::new(), 0, String::new(), 0, 0);
}

}