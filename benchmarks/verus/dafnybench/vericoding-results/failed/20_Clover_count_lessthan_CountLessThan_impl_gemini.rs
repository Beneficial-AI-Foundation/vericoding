// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [fixed incorrect std library lemma names] */
fn count_recursive_helper(s: Set<int>, threshold: int) -> (count: usize)
    ensures
        count == s.filter(|i: int| i < threshold).len(),
    decreases s.len()
{
    if s.is_empty() {
        0
    } else {
        let x = s.choose();
        let rest = s.remove(x);

        proof {
            let p = |i: int| i < threshold;
            vstd::set_lib::lemma_remove_insert(s, x);
            vstd::set_lib::lemma_filter_insert_distrib(rest, x, p);
            if p(x) {
                vstd::set_lib::lemma_filter_subset(rest, p);
                assert(!rest.filter(p).contains(x));
                vstd::set_lib::lemma_len_insert(rest.filter(p), x);
            }
        }

        let sub_count = count_recursive_helper(rest, threshold);

        if x < threshold {
            sub_count + 1
        } else {
            sub_count
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): [no changes, logic is in helper] */
{
    count_recursive_helper(numbers, threshold)
}
// </vc-code>

}
fn main() {}