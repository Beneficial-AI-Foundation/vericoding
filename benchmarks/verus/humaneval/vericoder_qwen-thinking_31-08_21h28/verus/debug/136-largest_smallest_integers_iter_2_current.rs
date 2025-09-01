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
    let mut largest_neg = None;
    let mut smallest_pos = None;
    let n = arr.len();
    let mut i = 0;
    while i < n {
        invariant {
            (largest_neg.is_none() 
                || (largest_neg.is_some() 
                    && (forall j: int, 0 <= j < i && arr@[j] < 0
                            #[trigger] (arr@[j] < 0)
                            ==> arr@[j] <= largest_neg.unwrap()
                    )
                )
            )
            &&
            (smallest_pos.is_none() 
                || (smallest_pos.is_some() 
                    && (forall j: int, 0 <= j < i && arr@[j] > 0
                            #[trigger] (arr@[j] > 0)
                            ==> smallest_pos.unwrap() <= arr@[j]
                    )
                )
            )
        }
        let current = arr[i];
        if current < 0 {
            if largest_neg.is_none() || current > largest_neg.unwrap() {
                largest_neg = Some(current);
            }
        } else if current > 0 {
            if smallest_pos.is_none() || current < smallest_pos.unwrap() {
                smallest_pos = Some(current);
            }
        }
        i += 1;
    }
    (largest_neg, smallest_pos)
}
// </vc-code>

fn main() {}
}