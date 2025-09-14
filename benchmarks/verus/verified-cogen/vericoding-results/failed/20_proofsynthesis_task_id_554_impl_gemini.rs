// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof body to the lemma to prove the postcondition */
proof fn lemma_filter_subrange_plus_one(s: Seq<u32>, i: int)
    requires 0 <= i < s.len()
    ensures
        s.subrange(0, i + 1).filter(|x: u32| x % 2 != 0) ==
            if s[i] % 2 != 0 {
                s.subrange(0, i).filter(|x: u32| x % 2 != 0).push(s[i])
            } else {
                s.subrange(0, i).filter(|x: u32| x % 2 != 0)
            }
{
    let p = |x: u32| x % 2 != 0;
    vstd::seq_lib::lemma_subrange_succ(s, 0, i);
    vstd::seq::lemma_filter_push(s.subrange(0, i), s[i], p);
}
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)

    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no logic change; verification depends on the now-proven helper lemma */
{
    let mut odd_numbers = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            odd_numbers@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i
    {
        let x = arr[i];
        if x % 2 != 0 {
            odd_numbers.push(x);
        }
        proof {
            lemma_filter_subrange_plus_one(arr@, i as int);
        }
        i = i + 1;
    }
    odd_numbers
}
// </vc-code>

}
fn main() {}