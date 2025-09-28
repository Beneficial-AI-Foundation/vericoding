// <vc-preamble>
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

        isSubstringPred(sub, str) ==> res,
        isSubstringPred(sub, str) ==> res,
        !res <==> isNotSubstringPred(sub, str),
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed a compilation error by replacing `==>` with `implies` in forall proof blocks. */
fn isPrefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> isPrefixPred(pre, str),
        !res <==> isNotPrefixPred(pre, str),
{
    if pre.len() > str.len() {
        return false;
    }
    if pre == str.subrange(0, pre.len() as int) {
        true
    } else {
        false
    }
}

fn isSubstring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        res <==> isSubstringPred(sub, str),
        res ==> isSubstringPred(sub, str),
        isSubstringPred(sub, str) ==> res,
        isSubstringPred(sub, str) ==> res,
        !res <==> isNotSubstringPred(sub, str),
{
    if sub.len() > str.len() {
        proof {
            assert(isNotSubstringPred(sub, str)) by {
                forall|j: int| 0 <= j <= str.len() as int implies isNotPrefixPred(sub, str.subrange(j, str.len() as int)) {
                    let suffix = str.subrange(j, str.len() as int);
                    assert(suffix.len() < sub.len());
                    isPrefix(sub, suffix);
                    assert(isNotPrefixPred(sub, suffix));
                }
            }
        }
        return false;
    }

    let mut i: int = 0;
    while i <= str.len() as int - sub.len() as int
        invariant
            0 <= i <= str.len() as int - sub.len() as int + 1,
            forall|j: int| 0 <= j < i ==> isNotPrefixPred(sub, str.subrange(j, str.len() as int)),
        decreases (str.len() as int - sub.len() as int) - i
    {
        if isPrefix(sub, str.subrange(i, str.len() as int)) {
            proof {
                assert(isSubstringPred(sub, str));
            }
            return true;
        }
        i = i + 1;
    }

    proof {
        assert(isNotSubstringPred(sub, str)) by {
            forall|j: int| 0 <= j <= str.len() as int implies isNotPrefixPred(sub, str.subrange(j, str.len() as int)) {
                if j <= str.len() as int - sub.len() as int {
                    assert(isNotPrefixPred(sub, str.subrange(j, str.len() as int)));
                } else {
                    let suffix = str.subrange(j, str.len() as int);
                    assert(suffix.len() < sub.len());
                    isPrefix(sub, suffix);
                    assert(isNotPrefixPred(sub, suffix));
                }
            }
        }
    }
    return false;
}
// </vc-helpers>

// <vc-spec>
fn haveCommonKSubstring(k: nat, str1: Seq<char>, str2: Seq<char>) -> (found: bool)
    ensures
        found <==> haveCommonKSubstringPred(k, str1, str2),
        !found <==> haveNotCommonKSubstringPred(k, str1, str2),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Strengthened proof blocks with by-clauses to guide verification. */
    if k > str1.len() {
        proof {
            assert(haveNotCommonKSubstringPred(k, str1, str2)) by {
                forall|i1: int, j1: int|
                    (0 <= i1 <= str1.len() as int - k as int && j1 == i1 + k as int)
                    implies isNotSubstringPred(str1.subrange(i1, j1), str2)
                {
                }
            }
        }
        return false;
    }

    let mut i: int = 0;
    while i <= str1.len() as int - k as int
        invariant
            0 <= i <= str1.len() as int - k as int + 1,
            k <= str1.len(),
            forall|j: int| 0 <= j < i ==> isNotSubstringPred(str1.subrange(j, j + k as int), str2),
        decreases (str1.len() as int - k as int) - i
    {
        let sub = str1.subrange(i, i + k as int);
        if isSubstring(sub, str2) {
            proof {
                assert(haveCommonKSubstringPred(k, str1, str2));
            }
            return true;
        }
        i = i + 1;
    }

    proof {
        assert(haveNotCommonKSubstringPred(k, str1, str2)) by {
            forall|i1: int, j1: int|
                (0 <= i1 <= str1.len() as int - k as int && j1 == i1 + k as int)
                implies isNotSubstringPred(str1.subrange(i1, j1), str2)
            {
                assert(isNotSubstringPred(str1.subrange(i1, j1), str2));
            }
        }
    }
    return false;
}
// </vc-code>

}
fn main() {}