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

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) && 
	pre == str.spec_index(..pre.len())
}
spec fn haveCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    exists i1, j1 :: 0 <= i1 <= str1.len()- k && j1 == i1 + k && isSubstringPred(str1.spec_index(i1..j1),str2)
}
spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall i1, j1 :: 0 <= i1 <= str1.len()- k && j1 == i1 + k ==> isNotSubstringPred(str1.spec_index(i1..j1),str2)
}
spec fn isSubstringPred(sub: String, str: String) -> bool {
    (exists i :: 0 <= i <= str.len() && isPrefixPred(sub, str.spec_index(i..)))
}
spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    (forall i :: 0 <= i <= str.len() ==> isNotPrefixPred(sub,str.spec_index(i..)))
}
spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) | 
	pre != str.spec_index(...len()pre|)
}

fn isSubstring(sub: String, str: String) -> (res: bool)
	ensures res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
  res: = false;
  assume res <==> isSubstringPred(sub, str);
  return res;
}


//ATOM

predicate isNotSubstringPred(sub: String, str: string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub, str[i..]))
}


//ATOM

method isPrefix(pre: String, str: string) returns (res:bool)
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

method haveCommonKSubstring(k: nat, str1: String, str2: string) returns (found: bool)
	ensures found <==> haveCommonKSubstringPred(k, str1, str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k, str1, str2) // This postcondition follows from the above lemma.
{
  found: = false;
  assume found <==> haveCommonKSubstringPred(k, str1, str2);
  return found;
}


// SPEC

method maxCommonSubstringLength(str1: String, str2: string) returns (len:nat)
    requires
        (str1.len() <= str2.len())
    ensures
        res <==> isSubstringPred(sub, str)
	//,
        !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.,
        !res <==> isNotPrefixPred(pre,str),
        res <==> isPrefixPred(pre,str),
        found <==> haveCommonKSubstringPred(k,str1,str2)
	//,
        !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.,
        (forall k :: len < k <= str1.len() ==> !haveCommonKSubstringPred(k,str1,str2)),
        haveCommonKSubstringPred(len,str1,str2)
{
    return (0, 0, 0, String::new(), 0, String::new(), 0, 0, 0, 0, String::new(), 0, String::new(), 0, 0, 0, 0, 0, 0, String::new(), 0);
}

}