// <vc-preamble>
use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min(a: int, b: int) -> int { if a < b { a } else { b } }
spec fn is_sorted(s: Seq<i32>) -> bool { forall |i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] <= s[j] }
// </vc-helpers>

// <vc-spec>
fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)

    ensures
        s@.len() == ret@.len(),
// </vc-spec>
// <vc-code>
{
    let mut ret: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            ret@.len() == i as nat,
        decreases s.len() - i
    {
        ret.push(s[i]);
        i = i + 1;
    }
    ret
}
// </vc-code>

}
fn main() {}