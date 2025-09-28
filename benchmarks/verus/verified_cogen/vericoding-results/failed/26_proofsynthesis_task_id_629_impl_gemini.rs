// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error in function type syntax */
proof fn filter_subrange_lemma(s: Seq<u32>, p: spec_fn(u32) -> bool, i: int)
    requires 0 <= i < s.len()
    ensures
        s.subrange(0, i + 1).filter(p) ==
            if p(s[i]) {
                s.subrange(0, i).filter(p).push(s[i])
            } else {
                s.subrange(0, i).filter(p)
            }
{
    vstd::seq_lib::lemma_filter_push(s.subrange(0, i), s[i], p);
}
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)

    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): correctly uses the fixed helper lemma */
{
    let mut even_numbers = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            even_numbers@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i,
    {
        let element = arr[i];
        if element % 2 == 0 {
            even_numbers.push(element);
        }
        proof {
            filter_subrange_lemma(arr@, |x: u32| x % 2 == 0, i as int);
        }
        i = i + 1;
    }
    even_numbers
}
// </vc-code>

}
fn main() {}