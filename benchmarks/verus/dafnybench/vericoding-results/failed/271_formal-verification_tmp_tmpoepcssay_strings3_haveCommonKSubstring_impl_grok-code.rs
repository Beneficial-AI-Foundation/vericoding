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
fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> isNotPrefixPred(pre, str),
        res <==> isPrefixPred(pre, str),
{
    if pre.len() > str.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < pre.len()
        invariant
            0 <= i <= pre.len(),
            forall|j: int| 0 <= j < i ==> pre@[j] == str@[j],
    {
        if pre@[i] != str@[i] {
            return false;
        }
        i = i + 1;
    }
    true
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str),
        res ==> isSubstringPred(sub, str),
        isSubstringPred(sub, str) ==> res,
        !res <==> isNotSubstringPred(sub, str),
{
    if sub.len() > str.len() {
        proof {
            assert(!isSubstringPred(sub, str));
        }
        return false;
    }
    let mut i: int = 0;
    while i <= str.len() - sub.len()
        invariant
            0 <= i <= str.len() - sub.len() + 1,
            forall|j: int| 0 <= j < i ==> !isPrefixPred(sub, str.subrange(j, str.len())),
    {
        if isPrefix(sub, str.subrange(i, str.len())) {
            proof {
                assert(isSubstringPred(sub, str));
            }
            return true;
        }
        i = i + 1;
    }
    proof {
        assert(!isSubstringPred(sub, str));
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
    if str1.len() < k {
        proof {
            assert(!haveCommonKSubstringPred(k, str1, str2));
        }
        return false;
    }
    let mut i1: int = 0;
    while i1 <= str1.len() - k
        invariant
            0 <= i1 <= str1.len() - k + 1,
            forall|idx: int| 0 <= idx < i1 ==> !isSubstringPred(str1.subrange(idx, idx + k), str2),
    {
        if isSubstring(str1.subrange(i1, i1 + k), str2) {
            proof {
                assert(haveCommonKSubstringPred(k, str1, str2));
            }
            return true;
        }
        i1 = i1 + 1;
    }
    proof {
        assert(!haveCommonKSubstringPred(k, str1, str2));
    }
    false
}
// </vc-code>

fn main() {}

}