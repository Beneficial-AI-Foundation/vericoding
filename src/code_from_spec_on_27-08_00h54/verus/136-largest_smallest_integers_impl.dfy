use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn has_negative(arr: Seq<i32>) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] < 0
}

spec fn has_positive(arr: Seq<i32>) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] > 0
}

spec fn is_largest_negative(arr: Seq<i32>, val: i32) -> bool {
    arr.contains(val) && val < 0 && forall|i: int| 0 <= i < arr.len() && arr[i] < 0 ==> arr[i] <= val
}

spec fn is_smallest_positive(arr: Seq<i32>, val: i32) -> bool {
    arr.contains(val) && val > 0 && forall|i: int| 0 <= i < arr.len() && arr[i] > 0 ==> arr[i] >= val
}
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
            0 <= i <= arr.len(),
            largest_neg.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] >= 0,
            largest_neg.is_some() ==> arr@.contains(largest_neg.unwrap()) && largest_neg.unwrap() < 0,
            largest_neg.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] < 0 ==> arr@[j] <= largest_neg.unwrap(),
            smallest_pos.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] <= 0,
            smallest_pos.is_some() ==> arr@.contains(smallest_pos.unwrap()) && smallest_pos.unwrap() > 0,
            smallest_pos.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] > 0 ==> arr@[j] >= smallest_pos.unwrap()
        decreases arr.len() - i
    {
        let val = arr[i];
        
        if val < 0 {
            if largest_neg.is_none() || val > largest_neg.unwrap() {
                largest_neg = Some(val);
            }
        } else if val > 0 {
            if smallest_pos.is_none() || val < smallest_pos.unwrap() {
                smallest_pos = Some(val);
            }
        }
        
        i += 1;
    }
    
    (largest_neg, smallest_pos)
}
// </vc-code>

}
fn main() {}