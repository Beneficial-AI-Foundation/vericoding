use vstd::prelude::*;

verus! {

// We spent 2h each on this assignment

// ATOM 
// We spent 2h each on this assignment

pub open spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool
{
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

// ATOM 

pub open spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool
{
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

//ATOM_PLACEHOLDER_PrefixNegationLemma

// SPEC 

pub fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str),
{
}

// ATOM 
pub open spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool
{
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len()))
}

// ATOM 

pub open spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool
{
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len()))
}

//ATOM_PLACEHOLDER_SubstringNegationLemma

// SPEC 

pub fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str),
        //!res <==> isNotSubstringPred(sub, str), // This postcondition follows from the above lemma.
{
}

//ATOM_PLACEHOLDER_haveCommonKSubstringPred

//ATOM_PLACEHOLDER_haveNotCommonKSubstringPred

//ATOM_PLACEHOLDER_commonKSubstringLemma

//ATOM_PLACEHOLDER_haveCommonKSubstring

//ATOM_PLACEHOLDER_maxCommonSubstringLength

}