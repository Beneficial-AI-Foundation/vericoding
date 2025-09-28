// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemmas to prove filter properties */
proof fn lemma_filter_push_odd(s: Seq<u32>, x: u32)
    requires x % 2 != 0
    ensures s.push(x).filter(|y: u32| y % 2 != 0) == s.filter(|y: u32| y % 2 != 0).push(x)
{
    assert(s.push(x).filter(|y: u32| y % 2 != 0) =~= s.filter(|y: u32| y % 2 != 0).push(x));
}

proof fn lemma_filter_push_even(s: Seq<u32>, x: u32)
    requires x % 2 == 0
    ensures s.push(x).filter(|y: u32| y % 2 != 0) == s.filter(|y: u32| y % 2 != 0)
{
    assert(s.push(x).filter(|y: u32| y % 2 != 0) =~= s.filter(|y: u32| y % 2 != 0));
}
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)

    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use helper lemmas to prove filter properties */
    let mut odd_list = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            odd_list@ == arr@.take(i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            odd_list.push(arr[i]);
            proof {
                assert(arr@.take((i + 1) as int) == arr@.take(i as int).push(arr@[i as int]));
                lemma_filter_push_odd(arr@.take(i as int), arr@[i as int]);
            }
        } else {
            proof {
                assert(arr@.take((i + 1) as int) == arr@.take(i as int).push(arr@[i as int]));
                lemma_filter_push_even(arr@.take(i as int), arr@[i as int]);
            }
        }
        i = i + 1;
    }
    assert(arr@.take(arr.len() as int) == arr@);
    odd_list
}
// </vc-code>

}
fn main() {}