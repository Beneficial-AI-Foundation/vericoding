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
spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) | 
	pre != str.index(...len()pre|)
}
spec fn isSubstringPred(sub: String, str: String) -> bool {
    (exists |i: int| 0 <= i <= str.len() &&  isPrefixPred(sub, str.index(i..)))
}
spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    (forall |i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub,str.index(i..)))
}
spec fn haveCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    exists |i1: int, j1: int| 0 <= i1 <= str1.len()- k && j1 == i1 + k && isSubstringPred(str1.index(i1..j1),str2)
}
spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall |i1: int, j1: int| 0 <= i1 <= str1.len()- k && j1 == i1 + k ==>  isNotSubstringPred(str1.index(i1..j1),str2)
}

spec fn spec_isPrefix(pre: String, str: String) -> res:bool
    ensures
        !res <==> isNotPrefixPred(pre,str),
        res <==> isPrefixPred(pre,str)
;

proof fn lemma_isPrefix(pre: String, str: String) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre,str),
        res <==> isPrefixPred(pre,str)
{
    false
}

}