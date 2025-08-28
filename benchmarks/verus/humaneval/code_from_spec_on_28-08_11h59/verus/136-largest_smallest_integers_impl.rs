use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr@.len(),
            largest_negative.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] >= 0,
            largest_negative.is_some() ==> arr@.contains(largest_negative.unwrap()) && largest_negative.unwrap() < 0,
            largest_negative.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] < 0 ==> arr@[j] <= largest_negative.unwrap(),
            smallest_positive.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] <= 0,
            smallest_positive.is_some() ==> arr@.contains(smallest_positive.unwrap()) && smallest_positive.unwrap() > 0,
            smallest_positive.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] > 0 ==> arr@[j] >= smallest_positive.unwrap(),
        decreases arr@.len() - i,
    {
        let val = arr[i];
        
        if val < 0 {
            match largest_negative {
                None => largest_negative = Some(val),
                Some(current) => {
                    if val > current {
                        largest_negative = Some(val);
                    }
                }
            }
        } else if val > 0 {
            match smallest_positive {
                None => smallest_positive = Some(val),
                Some(current) => {
                    if val < current {
                        smallest_positive = Some(val);
                    }
                }
            }
        }
        
        i += 1;
    }
    
    (largest_negative, smallest_positive)
}
// </vc-code>

}
fn main() {}