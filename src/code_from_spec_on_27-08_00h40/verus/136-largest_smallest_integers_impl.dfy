use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn has_negative(arr: &Vec<i32>) -> bool {
    exists|i: int| 0 <= i < arr@.len() && arr@[i] < 0
}

spec fn has_positive(arr: &Vec<i32>) -> bool {
    exists|i: int| 0 <= i < arr@.len() && arr@[i] > 0
}

spec fn is_largest_negative(arr: &Vec<i32>, val: i32) -> bool {
    val < 0 && arr@.contains(val) && 
    (forall|i: int| 0 <= i < arr@.len() && arr@[i] < 0 ==> arr@[i] <= val)
}

spec fn is_smallest_positive(arr: &Vec<i32>, val: i32) -> bool {
    val > 0 && arr@.contains(val) && 
    (forall|i: int| 0 <= i < arr@.len() && arr@[i] > 0 ==> arr@[i] >= val)
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
    let mut largest_negative: Option<i32> = None;
    let mut smallest_positive: Option<i32> = None;
    
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            largest_negative.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] >= 0,
            largest_negative.is_some() ==> {
                let val = largest_negative.unwrap();
                &&& val < 0
                &&& exists|j: int| 0 <= j < i && arr@[j] == val
                &&& forall|j: int| 0 <= j < i && arr@[j] < 0 ==> arr@[j] <= val
            },
            smallest_positive.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] <= 0,
            smallest_positive.is_some() ==> {
                let val = smallest_positive.unwrap();
                &&& val > 0
                &&& exists|j: int| 0 <= j < i && arr@[j] == val
                &&& forall|j: int| 0 <= j < i && arr@[j] > 0 ==> arr@[j] >= val
            }
    {
        let current = arr[i];
        
        if current < 0 {
            match largest_negative {
                None => {
                    largest_negative = Some(current);
                }
                Some(val) => {
                    if current > val {
                        largest_negative = Some(current);
                    }
                }
            }
        }
        
        if current > 0 {
            match smallest_positive {
                None => {
                    smallest_positive = Some(current);
                }
                Some(val) => {
                    if current < val {
                        smallest_positive = Some(current);
                    }
                }
            }
        }
        
        i = i + 1;
    }
    
    (largest_negative, smallest_positive)
}
// </vc-code>

}
fn main() {}