use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_largest_negative_preserved(arr: &Vec<i32>, largest_neg: Option<i32>, current: i32)
    requires
        largest_neg.is_some() ==> arr@.contains(largest_neg.unwrap()) && largest_neg.unwrap() < 0,
        largest_neg.is_some() ==> forall|i: int| 0 <= i < arr@.len() && arr@[i] < 0 ==> arr@[i] <= largest_neg.unwrap(),
        current >= 0,
    ensures
        largest_neg.is_some() ==> forall|i: int| 0 <= i < arr@.len() && arr@[i] < 0 ==> arr@[i] <= largest_neg.unwrap(),
{}

proof fn lemma_smallest_positive_preserved(arr: &Vec<i32>, smallest_pos: Option<i32>, current: i32)
    requires
        smallest_pos.is_some() ==> arr@.contains(smallest_pos.unwrap()) && smallest_pos.unwrap() > 0,
        smallest_pos.is_some() ==> forall|i: int| 0 <= i < arr@.len() && arr@[i] > 0 ==> arr@[i] >= smallest_pos.unwrap(),
        current <= 0,
    ensures
        smallest_pos.is_some() ==> forall|i: int| 0 <= i < arr@.len() && arr@[i] > 0 ==> arr@[i] >= smallest_pos.unwrap(),
{}
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
    let mut largest_neg: Option<i32> = None;
    let mut smallest_pos: Option<i32> = None;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr@.len(),
            largest_neg.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] >= 0,
            largest_neg.is_some() ==> arr@.contains(largest_neg.unwrap()) && largest_neg.unwrap() < 0,
            largest_neg.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] < 0 ==> arr@[j] <= largest_neg.unwrap(),
            smallest_pos.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] <= 0,
            smallest_pos.is_some() ==> arr@.contains(smallest_pos.unwrap()) && smallest_pos.unwrap() > 0,
            smallest_pos.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] > 0 ==> arr@[j] >= smallest_pos.unwrap(),
        decreases arr@.len() - i,
    {
        let current = arr[i];
        
        if current < 0 {
            if largest_neg.is_none() || current > largest_neg.unwrap() {
                largest_neg = Some(current);
            }
            proof {
                lemma_smallest_positive_preserved(arr, smallest_pos, current);
            }
        } else if current > 0 {
            if smallest_pos.is_none() || current < smallest_pos.unwrap() {
                smallest_pos = Some(current);
            }
            proof {
                lemma_largest_negative_preserved(arr, largest_neg, current);
            }
        } else {
            proof {
                lemma_largest_negative_preserved(arr, largest_neg, current);
                lemma_smallest_positive_preserved(arr, smallest_pos, current);
            }
        }
        
        i += 1;
    }
    
    (largest_neg, smallest_pos)
}
// </vc-code>

fn main() {}
}