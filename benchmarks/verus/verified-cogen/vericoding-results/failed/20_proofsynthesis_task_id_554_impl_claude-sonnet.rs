// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed seq indexing syntax */
spec fn is_odd(x: u32) -> bool { x % 2 != 0 }

proof fn filter_equivalence_lemma(arr: Seq<u32>, i: int, x: u32)
    requires 0 <= i < arr.len(),
             arr[i] == x
    ensures arr.subrange(0, i + 1).filter(|y: u32| y % 2 != 0) == 
            if x % 2 != 0 {
                arr.subrange(0, i).filter(|y: u32| y % 2 != 0).push(x)
            } else {
                arr.subrange(0, i).filter(|y: u32| y % 2 != 0)
            }
{
    proof {
        let prefix = arr.subrange(0, i);
        let extended = arr.subrange(0, i + 1);
        assert(extended == prefix.push(x));
        
        if x % 2 != 0 {
            assert(extended.filter(|y: u32| y % 2 != 0) == prefix.filter(|y: u32| y % 2 != 0).push(x));
        } else {
            assert(extended.filter(|y: u32| y % 2 != 0) == prefix.filter(|y: u32| y % 2 != 0));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)

    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed seq indexing syntax */
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        proof {
            filter_equivalence_lemma(arr@, i as int, arr@[i as int]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}