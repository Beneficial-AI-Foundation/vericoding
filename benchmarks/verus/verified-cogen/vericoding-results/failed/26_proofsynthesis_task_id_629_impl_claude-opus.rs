// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)

    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed move error by removing unnecessary old_even variable */
    let mut even_numbers = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            even_numbers@ == arr@.take(i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 == 0 {
            even_numbers.push(arr[i]);
            proof {
                assert(arr@.take((i + 1) as int) == arr@.take(i as int).push(arr@[i as int]));
                assert(arr@[i as int] % 2 == 0);
            }
        } else {
            proof {
                assert(arr@.take((i + 1) as int) == arr@.take(i as int).push(arr@[i as int]));
                assert(arr@[i as int] % 2 != 0);
            }
        }
        i += 1;
    }
    assert(arr@.take(arr.len() as int) == arr@);
    even_numbers
}
// </vc-code>

}
fn main() {}