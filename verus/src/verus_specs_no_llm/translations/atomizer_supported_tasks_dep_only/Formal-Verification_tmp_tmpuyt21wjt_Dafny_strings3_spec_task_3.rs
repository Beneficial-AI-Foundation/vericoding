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
spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) | 
	pre != str.spec_index(...len()pre|)
}
spec fn isSubstringPred(sub: String, str: String) -> bool {
    (exists i :: 0 <= i <= str.len() &&  isPrefixPred(sub, str.spec_index(i..)))
}
spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    (forall i :: 0 <= i <= str.len() ==> isNotPrefixPred(sub,str.spec_index(i..)))
}
spec fn haveCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    exists i1, j1 :: 0 <= i1 <= str1.len()- k && j1 == i1 + k && isSubstringPred(str1.spec_index(i1..j1),str2)
}
spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall i1, j1 :: 0 <= i1 <= str1.len()- k && j1 == i1 + k ==>  isNotSubstringPred(str1.spec_index(i1..j1),str2)
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre,str),
        res <==> isPrefixPred(pre,str)
{
    return false;
}

}