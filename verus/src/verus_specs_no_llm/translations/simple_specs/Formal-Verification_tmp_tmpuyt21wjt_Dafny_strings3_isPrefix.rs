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

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre,str),
        res <==> isPrefixPred(pre,str)
{
    return false;
}

}