// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simple predicates for negative and positive integers */
spec fn is_negative(x: i32) -> bool { x < 0 }
spec fn is_positive(x: i32) -> bool { x > 0 }
// </vc-helpers>

// <vc-spec>
fn largest_smallest_integers(arr: &Vec<i32>) -> (res: (Option<i32>, Option<i32>))

    ensures
        ({
            let a = res.0;
            let b = res.1;
            &&& a.is_none() ==> forall|i: int| 0 <= i < arr@.len() ==> arr@[i] >= 0
            &&& a.is_some() ==> arr@.contains(a.unwrap()) && a.unwrap() < 0
            &&& a.is_some() ==> forall|i: int|
                0 <= i < arr@.len() && arr@[i] < 0 ==> arr@[i] <= a.unwrap()
            &&& b.is_none() ==> forall|i: int| 0 <= i < arr@.len() ==> arr@[i] <= 0
            &&& b.is_some() ==> arr@.contains(b.unwrap()) && b.unwrap() > 0
            &&& b.is_some() ==> forall|i: int|
                0 <= i < arr@.len() && arr@[i] > 0 ==> arr@[i] >= b.unwrap()
        }),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): iterate array preserving invariants and assert bounds before accesses */
    let n: usize = arr.len();
    let mut ui: usize = 0;
    let mut max_neg: Option<i32> = None;
    let mut min_pos: Option<i32> = None;

    while ui < n
        invariant
            0 <= (ui as int) && (ui as int) <= arr@.len(),
            (n as int) == arr@.len(),
            max_neg.is_none() ==> forall|k: int| 0 <= k < (ui as int) ==> arr@[k] >= 0,
            max_neg.is_some() ==> arr@.contains(max_neg.unwrap()) && max_neg.unwrap() < 0,
            max_neg.is_some() ==> forall|k: int| 0 <= k < (ui as int) && arr@[k] < 0 ==> arr@[k] <= max_neg.unwrap(),
            min_pos.is_none() ==> forall|k: int| 0 <= k < (ui as int) ==> arr@[k] <= 0,
            min_pos.is_some() ==> arr@.contains(min_pos.unwrap()) && min_pos.unwrap() > 0,
            min_pos.is_some() ==> forall|k: int| 0 <= k < (ui as int) && arr@[k] > 0 ==> arr@[k] >= min_pos.unwrap(),
        decreases
            n - ui
    {
        let x: i32 = arr[ui];

        if x < 0 {
            match max_neg {
                None => {
                    max_neg = Some(x);
                    proof {
                        assert((ui as int) < arr@.len());
                        assert(arr@[(ui as int)] == x);
                    }
                }
                Some(m) => {
                    if x > m {
                        max_neg = Some(x);
                        proof {
                            assert((ui as int) < arr@.len());
                            assert(arr@[(ui as int)] == x);
                        }
                    }
                }
            }
        } else if x > 0 {
            match min_pos {
                None => {
                    min_pos = Some(x);
                    proof {
                        assert((ui as int) < arr@.len());
                        assert(arr@[(ui as int)] == x);
                    }
                }
                Some(m) => {
                    if x < m {
                        min_pos = Some(x);
                        proof {
                            assert((ui as int) < arr@.len());
                            assert(arr@[(ui as int)] == x);
                        }
                    }
                }
            }
        }

        ui = ui + 1;
    }

    (max_neg, min_pos)
}
// </vc-code>

}
fn main() {}