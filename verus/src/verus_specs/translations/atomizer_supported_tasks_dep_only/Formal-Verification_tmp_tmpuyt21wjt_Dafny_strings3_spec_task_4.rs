use vstd::prelude::*;

verus! {

spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

pub fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str)
{
}

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len()))
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len()))
}

pub fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str)
{
}

spec fn haveCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && isSubstringPred(str1.subrange(i1, j1), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> isNotSubstringPred(str1.subrange(i1, j1), str2)
}

pub fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> haveCommonKSubstringPred(k, str1, str2)
{
}

pub fn maxCommonSubstringLength(str1: Seq<char>, str2: Seq<char>) -> (len: nat)
    requires
        str1.len() <= str2.len()
    ensures
        forall|k: int| len < k <= str1.len() ==> !haveCommonKSubstringPred(k as nat, str1, str2),
        haveCommonKSubstringPred(len, str1, str2)
{
}

}