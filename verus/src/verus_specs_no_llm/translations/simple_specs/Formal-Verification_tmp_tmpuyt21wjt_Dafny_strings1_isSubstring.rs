// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isSubstringPredicate(sub: String, str: String) -> bool {
    str.len() >= sub.len() && (exists |i: int| 0 <= i <= str.len() && isPrefixPredicate(sub, str.index(i..)))
}
spec fn isPrefixPredicate(pre: String, str: String) -> bool {
    str.len() >= pre.len() && pre <= str
}

spec fn spec_isPrefix(pre: String, str: String) -> res: bool)
 ensures |pre| > |str| ==> !res
 ensures res == isPrefixPredicate(pre, str)
{
  res := false;
  assume |pre| > |str| ==> !res;
  assume res ==> isPrefixPredicate(pre, str);
  return res;
}


//ATOM

predicate isSubstringPredicate (sub: string, str:string)
{
 |str| >= |sub| && (exists i :: 0 <= i <= |str| && isPrefixPredicate(sub, str[i..]))
}


//ATOM
predicate isPrefixPredicate(pre: string, str:string)
{
 |str| >= |pre| && pre <= str
}


// SPEC

method isSubstring(sub: string, str: string) returns (res:bool
    ensures
        pre.len() > str.len() ==> !res,
        res == isPrefixPredicate(pre, str),
        res == isSubstringPredicate(sub, str)
;

proof fn lemma_isPrefix(pre: String, str: String) -> (res: bool)
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
    (0, 0, String::new(), 0, String::new(), 0, 0)
}

}