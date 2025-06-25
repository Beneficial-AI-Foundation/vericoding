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
spec fn isSubstringPred(sub: String, str: String) -> bool {
    (exists|i: int| 0 <= i <= str.len() and  isPrefixPred(sub, str[i..]))
}
spec fn isNotSubstringPred(sub: String, str: String) -> bool {
    (forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub,str[i..]))
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures !res <==> isNotPrefixPred(pre,str),
            res <==> isPrefixPred(pre,str)
{
}

}