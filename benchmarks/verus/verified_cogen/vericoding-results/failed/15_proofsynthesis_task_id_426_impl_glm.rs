// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma_filter_concat for sequence filter concatenation */
proof fn lemma_filter_concat<A>(s1: Seq<A>, s2: Seq<A>, p: spec_fn(A) -> bool)
    ensures s1.concat(s2).filter(p) == s1.filter(p).concat(s2.filter(p))
{
    vstd::seq::lemma_filter_concat(s1, s2, p);
}
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)

    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed incorrect ghost keyword in assignment */
{
    let mut odd_list = Vec::new();
    let mut i = 0;

    while i < arr.len()
        invariant
            i <= arr@.len(),
            odd_list@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr@.len() - (i as int)
    {
        let x = arr[i];
        proof {
            let old_i = i;
            let old_odd_list = odd_list@;
            let subrange_before = arr@.subrange(0, old_i as int);
            let subrange_after = arr@.subrange(0, (old_i+1) as int);
            assert(subrange_after == subrange_before + seq![x]);
        }
        if x % 2 != 0 {
            odd_list.push(x);
            proof {
                assert(odd_list@ == old_odd_list + seq![x]);
                lemma_filter_concat(subrange_before, seq![x], |p| p % 2 != 0);
            }
        } else {
            proof {
                assert(odd_list@ == old_odd_list);
                lemma_filter_concat(subrange_before, seq![x], |p| p % 2 != 0);
            }
        }
        i += 1;
    }

    odd_list
}
// </vc-code>

}
fn main() {}