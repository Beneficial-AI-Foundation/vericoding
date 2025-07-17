// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
	pre == str.index(..pre.len())
}
spec fn isSubstringPred(sub: String, str: String) -> bool {
    (exists |i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.index(i..)))
}
spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) | 
	pre != str.index(...len()pre|)
}
spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    (forall |i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub,str.index(i..)))
}

spec fn spec_isPrefix(pre: String, str: String) -> res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures res <==> isPrefixPred(pre,str)
{
  res := false;
  assume !res <==> isNotPrefixPred(pre,str);
  assume res <==> isPrefixPred(pre,str);
  return res;
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


// SPEC

method isSubstring(sub: string, str: string) returns (res:bool
    ensures
        !res <==> isNotPrefixPred(pre,str),
        res <==> isPrefixPred(pre,str),
        res <==> isSubstringPred(sub, str)
	//,
        !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
;

proof fn lemma_isPrefix(pre: String, str: String) -> (res: bool)
	ensures !res <==> isNotPrefixPred(pre, str)
	ensures res <==> isPrefixPred(pre, str)
{
  res: = false;
  assume !res <==> isNotPrefixPred(pre, str);
  assume res <==> isPrefixPred(pre, str);
  return res;
}


//ATOM

predicate isNotPrefixPred(pre: String, str: string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}


//ATOM

predicate isNotSubstringPred(sub:string, str: string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub, str[i..]))
}


// SPEC

method isSubstring(sub: String, str: string) returns (res:bool)
    ensures
        !res <==> isNotPrefixPred(pre,str),
        res <==> isPrefixPred(pre,str),
        res <==> isSubstringPred(sub, str)
	//,
        !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
    (0, 0, 0, 0, String::new(), 0, 0, String::new(), 0)
}

}