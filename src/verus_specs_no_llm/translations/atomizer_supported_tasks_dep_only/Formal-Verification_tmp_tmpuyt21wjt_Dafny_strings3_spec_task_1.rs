// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn isPrefixPred(pre: String, str: String) -> bool {
    (pre.len() <= str.len()) and 
	pre == str[..pre.len()]
}
spec fn isNotPrefixPred(pre: String, str: String) -> bool {
    (pre.len() > str.len()) | 
	pre != str[...len()pre|]
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures !res <==> isNotPrefixPred(pre,str),
            res <==> isPrefixPred(pre,str)
{
}

}