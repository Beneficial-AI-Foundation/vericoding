use vstd::prelude::*;

verus! {

fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str),
{
    assume(false);
    true
}



spec fn isPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() <= str.len()) && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn isNotPrefixPred(pre: Seq<char>, str: Seq<char>) -> bool {
    (pre.len() > str.len()) || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn isSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && isPrefixPred(sub, str.subrange(i, str.len() as int))
}

spec fn isNotSubstringPred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> isNotPrefixPred(sub, str.subrange(i, str.len() as int))
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str),
        res ==> isSubstringPred(sub, str),
        // ensures  !res ==> !isSubstringPred(sub, str)
        isSubstringPred(sub, str) ==> res,
        isSubstringPred(sub, str) ==> res,
        !res <==> isNotSubstringPred(sub, str), // This postcondition follows from the above lemma.
{
    assume(false);
    true
}



spec fn haveCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && isSubstringPred(str1.subrange(i1, j1), str2)
}

spec fn haveNotCommonKSubstringPred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> isNotSubstringPred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
fn is_substring_of_length_k(sub: Seq<char>, str: Seq<char>, k: nat) -> (res: bool)
    requires
        sub.len() == k,
    ensures
        res <==> isSubstringPred(sub, str),
{
    let mut i = 0;
    while i <= (str.len() - k) as int
        invariant
            0 <= i <= (str.len() - k) as int + 1,
            forall|j: int| 0 <= j < i ==> sub != str.subrange(j, j + (k as int)),
    {
        if isPrefix(sub, str.subrange(i, i + (k as int))) {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> haveCommonKSubstringPred(k, str1, str2),
        !found <==> haveNotCommonKSubstringPred(k, str1, str2), // This postcondition follows from the above lemma.
// </vc-spec>
// <vc-code>
{
    let mut found = false;
    let mut i1 = 0;
    while i1 <= (str1.len() - k) as int
        invariant
            0 <= i1 <= (str1.len() - k) as int + 1,
            forall|j: int| 0 <= j < i1 ==> isNotSubstringPred(str1.subrange(j, j + (k as int)), str2),
    {
        if is_substring_of_length_k(str1.subrange(i1, i1 + (k as int)), str2, k) {
            return true;
        }
        i1 += 1;
    }
    false
}
// </vc-code>

fn main() {}

}