// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive filter_prefix building sequence of odd elements */
spec fn filter_prefix(s: Seq<u32>, i: nat) -> Seq<u32> { if i == 0 { Seq::empty() } else { let prev = filter_prefix(s, i - 1); let x = s@[i - 1]; if x % 2 != 0 { prev + Seq::new(1usize, |_: nat| x) } else { prev } } }

/* helper modified by LLM (iteration 5): simple odd predicate */
spec fn is_odd(x: u32) -> bool { x % 2 != 0 }
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)

    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement loop accumulating odd numbers and maintaining invariant with filter_prefix */
    let mut res = Vec::<u32>::new();
    let mut i: nat = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            res@ == filter_prefix(arr@, i),
        decreases arr.len() - i
    {
        let v = arr[i];
        if is_odd(v) {
            res.push(v);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}