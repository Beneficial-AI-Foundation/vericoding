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
spec fn haveCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len()- k and j1 == i1 + k and isSubstringPred(str1[i1..j1],str2)
}
spec fn haveNotCommonKSubstringPred(k: nat, str1: String, str2: String) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len()- k and j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    ensures !res <==> isNotPrefixPred(pre,str),
            res <==> isPrefixPred(pre,str)
{
}

}