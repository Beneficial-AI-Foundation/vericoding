// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn clip_value(val: i8, min_val: i8, max_val: i8) -> (result: i8)
    ensures
        if (min_val as int) <= (max_val as int) {
            if (val as int) < (min_val as int) {
                (result as int) == (min_val as int)
            } else if (val as int) > (max_val as int) {
                (result as int) == (max_val as int)
            } else {
                (result as int) == (val as int)
            }
        } else {
            (result as int) == (max_val as int)
        }
{
    if min_val <= max_val {
        if val < min_val {
            min_val
        } else if val > max_val {
            max_val
        } else {
            val
        }
    } else {
        max_val
    }
}
// </vc-helpers>

// <vc-spec>
fn clip(arr: &Vec<i8>, min_val: i8, max_val: i8) -> (result: Vec<i8>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            if (min_val as int) <= (max_val as int) {
                if (arr[i] as int) < (min_val as int) {
                    (result[i] as int) == (min_val as int)
                } else if (arr[i] as int) > (max_val as int) {
                    (result[i] as int) == (max_val as int)
                } else {
                    (result[i] as int) == (arr[i] as int)
                }
            } else {
                (result[i] as int) == (max_val as int)
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            result.len() == i,
            i <= arr.len(),
            forall|j: int| 0 <= j < i ==> {
                if (min_val as int) <= (max_val as int) {
                    if (arr[j] as int) < (min_val as int) {
                        (result[j] as int) == (min_val as int)
                    } else if (arr[j] as int) > (max_val as int) {
                        (result[j] as int) == (max_val as int)
                    } else {
                        (result[j] as int) == (arr[j] as int)
                    }
                } else {
                    (result[j] as int) == (max_val as int)
                }
            },
        decreases arr.len() - i
    {
        let clipped = clip_value(arr[i], min_val, max_val);
        result.push(clipped);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}