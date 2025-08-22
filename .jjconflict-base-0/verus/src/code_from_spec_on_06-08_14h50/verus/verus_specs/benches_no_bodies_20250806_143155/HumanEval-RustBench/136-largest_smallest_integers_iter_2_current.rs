use vstd::prelude::*;

verus! {

fn largest_smallest_integers(arr: &Vec<i32>) -> (res: (Option<i32>, Option<i32>))
    // post-conditions-start
    ensures
        ({
            let (a, b) = res;
            // If a is Some, it must be negative and in the array
            (a.is_some() ==> (a.unwrap() < 0 && arr@.contains(a.unwrap()))) &&
            // If a is Some, it must be the largest (closest to 0) negative number
            (a.is_some() ==> forall|x: i32| arr@.contains(x) && x < 0 ==> x <= a.unwrap()) &&
            // If a is None, there are no negative numbers in the array
            (a.is_none() ==> forall|x: i32| arr@.contains(x) ==> x >= 0) &&
            
            // If b is Some, it must be positive and in the array  
            (b.is_some() ==> (b.unwrap() > 0 && arr@.contains(b.unwrap()))) &&
            // If b is Some, it must be the smallest positive number
            (b.is_some() ==> forall|x: i32| arr@.contains(x) && x > 0 ==> x >= b.unwrap()) &&
            // If b is None, there are no positive numbers in the array
            (b.is_none() ==> forall|x: i32| arr@.contains(x) ==> x <= 0)
        }),
    // post-conditions-end
{
    // impl-start
    let mut i: usize = 0;
    let mut a = None;
    let mut b = None;

    /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
    while i < arr.len()
        // invariants-start
        invariant
            0 <= i <= arr@.len(),
            a.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] >= 0,
            a.is_some() ==> arr@.contains(a.unwrap()) && a.unwrap() < 0,
            a.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] < 0 ==> arr@[j] <= a.unwrap(),
            b.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] <= 0,
            b.is_some() ==> arr@.contains(b.unwrap()) && b.unwrap() > 0,
            b.is_some() ==> forall|j: int| 0 <= j < i && arr@[j] > 0 ==> arr@[j] >= b.unwrap(),
        // invariants-end
        decreases arr@.len() - i
    {
        if arr[i] < 0 && (a.is_none() || arr[i] >= a.unwrap()) {
            a = Some(arr[i]);
        }
        if arr[i] > 0 && (b.is_none() || arr[i] <= b.unwrap()) {
            b = Some(arr[i]);
        }
        i = i + 1;
    }
    (a, b)
    // impl-end
}

}
fn main() {}