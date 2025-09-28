// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn clip_helper_lemma(arr: Seq<i8>, min_val: i8, max_val: i8, i: int)
    requires
        0 <= i < arr.len(),
    ensures
        if min_val <= max_val {
            if arr[i] < min_val {
                min_val <= max_val
            } else if arr[i] > max_val {
                min_val <= max_val
            } else {
                arr[i] >= min_val && arr[i] <= max_val
            }
        } else {
            true
        }
{
    if min_val <= max_val {
        if arr[i] < min_val {
            assert(min_val <= max_val);
        } else if arr[i] > max_val {
            assert(min_val <= max_val);
        } else {
            assert(arr[i] >= min_val && arr[i] <= max_val);
        }
    } else {
        assert(true);
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
    /* code modified by LLM (iteration 4): Fix ensures clause by properly handling index bounds */
    let mut result = Vec::new();
    let mut index: usize = 0;
    
    while index < arr.len()
        invariant
            result.len() == index,
            forall|j: int| 0 <= j < index ==> {
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
            index <= arr.len()
        decreases arr.len() - index
    {
        let current_val = arr[index];
        let clipped_val = if min_val <= max_val {
            if current_val < min_val {
                min_val
            } else if current_val > max_val {
                max_val
            } else {
                current_val
            }
        } else {
            max_val
        };
        
        result.push(clipped_val);
        index += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}