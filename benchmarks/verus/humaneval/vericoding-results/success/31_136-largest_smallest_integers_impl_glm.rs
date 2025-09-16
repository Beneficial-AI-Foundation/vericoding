// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains_negative(arr: &Vec<i32>) -> bool {
    exists|i: int| 0 <= i < arr@.len() && arr@[i] < 0
}

spec fn contains_positive(arr: &Vec<i32>) -> bool {
    exists|i: int| 0 <= i < arr@.len() && arr@[i] > 0
}

/* helper modified by LLM (iteration 3): fixed helper definitions to work with partial arrays */
spec fn is_largest_negative_partial(arr: &Vec<i32>, x: i32, end: int) -> bool {
    x < 0 && exists|i: int| 0 <= i < end && arr@[i] == x &&
    forall|j: int| 0 <= j < end && arr@[j] < 0 ==> arr@[j] <= x
}

spec fn is_smallest_positive_partial(arr: &Vec<i32>, x: i32, end: int) -> bool {
    x > 0 && exists|i: int| 0 <= i < end && arr@[i] == x &&
    forall|j: int| 0 <= j < end && arr@[j] > 0 ==> arr@[j] >= x
}

spec fn is_largest_negative(arr: &Vec<i32>, x: i32) -> bool {
    is_largest_negative_partial(arr, x, arr@.len() as int)
}

spec fn is_smallest_positive(arr: &Vec<i32>, x: i32) -> bool {
    is_smallest_positive_partial(arr, x, arr@.len() as int)
}
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
    /* code modified by LLM (iteration 4): fixed type mismatch in loop invariant */
    let mut largest_negative: Option<i32> = None;
    let mut smallest_positive: Option<i32> = None;
    
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            largest_negative.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] >= 0,
            largest_negative.is_some() ==> is_largest_negative_partial(arr, largest_negative.unwrap(), i as int),
            smallest_positive.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] <= 0,
            smallest_positive.is_some() ==> is_smallest_positive_partial(arr, smallest_positive.unwrap(), i as int),
        decreases (arr.len() - i)
    {
        let value = arr[i];
        if value < 0 {
            if largest_negative.is_none() || value > largest_negative.unwrap() {
                largest_negative = Some(value);
            }
        } else if value > 0 {
            if smallest_positive.is_none() || value < smallest_positive.unwrap() {
                smallest_positive = Some(value);
            }
        }
        i += 1;
    }
    
    (largest_negative, smallest_positive)
}
// </vc-code>

}
fn main() {}