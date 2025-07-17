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