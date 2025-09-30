// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): element-wise clipping helper using i8 */
fn clip_elem(x: i8, min_val: i8, max_val: i8) -> (res: i8)
    ensures
        if (min_val as int) <= (max_val as int) {
            if (x as int) < (min_val as int) {
                (res as int) == (min_val as int)
            } else if (x as int) > (max_val as int) {
                (res as int) == (max_val as int)
            } else {
                (res as int) == (x as int)
            }
        } else {
            (res as int) == (max_val as int)
        },
{
    if min_val <= max_val {
        if x < min_val {
            return min_val;
        } else if x > max_val {
            return max_val;
        } else {
            return x;
        }
    } else {
        return max_val;
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
    /* code modified by LLM (iteration 4): use spec indexing (arr@, result@) in invariant to avoid usize/int mismatch */
    let mut result = Vec::<i8>::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> {
                if (min_val as int) <= (max_val as int) {
                    if (arr@[j] as int) < (min_val as int) {
                        (result@[j] as int) == (min_val as int)
                    } else if (arr@[j] as int) > (max_val as int) {
                        (result@[j] as int) == (max_val as int)
                    } else {
                        (result@[j] as int) == (arr@[j] as int)
                    }
                } else {
                    (result@[j] as int) == (max_val as int)
                }
            },
        decreases arr.len() - i
    {
        let x: i8 = arr[i];
        let c: i8 = clip_elem(x, min_val, max_val);
        result.push(c);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}