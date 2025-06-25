// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre,str),
        res <==> isPrefixPred(pre,str)
{
    return false;
}

}