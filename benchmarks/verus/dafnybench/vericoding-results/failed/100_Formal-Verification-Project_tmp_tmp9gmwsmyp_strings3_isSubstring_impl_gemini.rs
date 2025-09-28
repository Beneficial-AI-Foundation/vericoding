// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures 
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
{
    assume(false);
    false
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_substring(sub: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures res <==> is_substring_pred(sub, str)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type mismatches by using 'int' for the loop counter and adding casts */
{
    let mut i: int = 0;
    while i <= str.len() as int
        invariant
            0 <= i && i <= str.len() as int + 1,
            forall|j: int| 0 <= j < i ==> is_not_prefix_pred(sub, str.subrange(j, str.len() as int)),
        decreases (str.len() as int) - i
    {
        let ghost suffix = str.subrange(i, str.len() as int);
        if is_prefix(sub, suffix) {
            proof {
                assert(is_prefix_pred(sub, suffix));
                assert(is_substring_pred(sub, str));
            }
            return true;
        }
        i = i + 1;
    }

    proof {
        assert(is_not_substring_pred(sub, str));
    }

    false
}
// </vc-code>

}
fn main() {}