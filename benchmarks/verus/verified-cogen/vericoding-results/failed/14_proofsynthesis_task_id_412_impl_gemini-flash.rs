// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)

    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous implementation had a type mismatch error where `arr@.take` expected an `int` but received a `nat`. The `take` function on `Seq<T>` takes an `int` as an argument. The fix involves casting `i` (which is a `usize`) to `int` instead of `nat` when calling `take`. */
{
        let mut even_list: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        while i < arr.len()
            invariant
                0 <= i && i <= arr.len(),
                even_list@ == arr@.take(i as int).filter(|x: u32| (x % 2) == 0)
        {
            let x = arr[i];
            if x % 2 == 0 {
                even_list.push(x);
            }
            i = i + 1;
        }
        even_list
    }
// </vc-code>

}
fn main() {}