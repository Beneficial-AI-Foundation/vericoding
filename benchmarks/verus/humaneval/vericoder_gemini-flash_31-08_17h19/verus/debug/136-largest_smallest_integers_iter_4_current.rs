use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn largest_smallest_integers(arr: &Vec<i32>) -> (res: (Option<i32>, Option<i32>))
    // post-conditions-start
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
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut largest_negative: Option<i32> = None;
    let mut smallest_positive: Option<i32> = None;

    let arr_seq = arr.view();
    let len = arr_seq.len();

    let mut i: int = 0;
    while i < len as int
        invariant
            0 <= i <= len as int, // i should be within bounds
            largest_negative.is_none() || (
                largest_negative.is_some() &&
                largest_negative.unwrap() < 0 &&
                ({ // This ensures the `largest_negative.unwrap()` value was initially from the array
                    let val = largest_negative.unwrap();
                    exists |k: int| 0 <= k < i && arr_seq.index(k as nat) == val
                }) &&
                forall|j: int| #![trigger arr_seq.index(j as nat)] 0 <= j < i && arr_seq.index(j as nat) < 0 ==> arr_seq.index(j as nat) <= largest_negative.unwrap()
            ),
            smallest_positive.is_none() || (
                smallest_positive.is_some() &&
                smallest_positive.unwrap() > 0 &&
                ({ // This ensures the `smallest_positive.unwrap()` value was initially from the array
                    let val = smallest_positive.unwrap();
                    exists |k: int| 0 <= k < i && arr_seq.index(k as nat) == val
                }) &&
                forall|j: int| #![trigger arr_seq.index(j as nat)] 0 <= j < i && arr_seq.index(j as nat) > 0 ==> arr_seq.index(j as nat) >= smallest_positive.unwrap()
            ),
    {
        let val = arr_seq.index(i as nat);

        if val < 0 {
            if largest_negative.is_none() {
                largest_negative = Some(val);
            } else {
                let current_largest = largest_negative.unwrap();
                if val > current_largest {
                    largest_negative = Some(val);
                }
            }
        } else if val > 0 {
            if smallest_positive.is_none() {
                smallest_positive = Some(val);
            } else {
                let current_smallest = smallest_positive.unwrap();
                if val < current_smallest {
                    smallest_positive = Some(val);
                }
            }
        }
        i = i + 1;
    }

    (largest_negative, smallest_positive)
}
// </vc-code>

fn main() {}
}