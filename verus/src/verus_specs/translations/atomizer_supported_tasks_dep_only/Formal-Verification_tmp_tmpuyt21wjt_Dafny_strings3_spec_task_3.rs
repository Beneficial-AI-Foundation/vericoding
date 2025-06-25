use vstd::prelude::*;

verus! {

// ATOM 
// We spent 2h each on this assignment

spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool
{
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

// ATOM 

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool
{
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

//ATOM_PLACEHOLDER_PrefixNegationLemma

// SPEC 

pub fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str)
{
}

// ATOM 
spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool
{
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len()))
}

// ATOM 

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool
{
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len()))
}

//ATOM_PLACEHOLDER_SubstringNegationLemma

// SPEC 

pub fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str)
        //ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
}

// ATOM 

spec fn haveCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool
{
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && isSubstringPred(str1.subrange(i1, j1), str2)
}

// ATOM 

spec fn haveNotCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool
{
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> isNotSubstringPred(str1.subrange(i1, j1), str2)
}

//ATOM_PLACEHOLDER_commonKSubstringLemma

// SPEC 

pub fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> haveCommonKSubstringPred(k, str1, str2)
        //ensures !found <==> haveNotCommonKSubstringPred(k, str1, str2) // This postcondition follows from the above lemma.
{
}

//ATOM_PLACEHOLDER_maxCommonSubstringLength

}