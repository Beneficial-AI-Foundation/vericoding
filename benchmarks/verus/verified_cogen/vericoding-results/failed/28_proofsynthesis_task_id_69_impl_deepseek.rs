// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove syntax errors and fix helper functions */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
spec fn is_subrange(s1: Seq<int>, s2: Seq<int>) -> bool {
    exists|k: int| 
        0 <= k && k <= s1.len() - s2.len() && 
        s1.subrange(k, k + s2.len()) === s2
}
proof fn subrange_empty_seq() 
    ensures 
        forall|s: Seq<int>| is_subrange(s, Seq::empty())
{
    assert forall|s: Seq<int>| is_subrange(s, Seq::empty()) by {
        assert(s.subrange(0, 0) === Seq::empty());
        assert(0 <= 0 && 0 <= s.len() - 0);
    };
}
proof fn subrange_equal_seqs() 
    ensures 
        forall|s: Seq<int>| is_subrange(s, s)
{
    assert forall|s: Seq<int>| is_subrange(s, s) by {
        assert(s.subrange(0, s.len()) === s);
        assert(0 <= 0 && 0 <= s.len() - s.len());
    };
}
// </vc-helpers>

// <vc-spec>
fn is_sub_list(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)

    requires
        sub.len() <= main.len(),

    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix loop invariant syntax by removing extra lines */
{
    if sub.is_empty() {
        return true;
    }
    let mut i = 0;
    while i <= main.len() - sub.len() {
        invariant
            0 <= i <= main.len() - sub.len() + 1,
            forall|j: int| 0 <= j < i ==> !(main@.subrange(j, j + sub.len()) =~= sub@);
        let mut match_found = true;
        let mut j = 0;
        while j < sub.len() {
            invariant
                0 <= j <= sub.len(),
                match_found == (forall|k: int| 0 <= k < j ==> main@[i + k] == sub@[k]);
            if main[i + j] != sub[j] {
                match_found = false;
                break;
            }
            j += 1;
        }
        if match_found {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>

}
fn main() {}