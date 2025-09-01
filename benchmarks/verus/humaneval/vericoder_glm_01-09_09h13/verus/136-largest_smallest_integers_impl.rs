use vstd::prelude::*;

verus! {

// <vc-helpers>
// (empty)
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
    let mut max_neg: Option<i32> = None;
    let mut min_pos: Option<i32> = None;

    for i in 0..arr.len()
        invariant
            0 <= i <= arr@.len(),
            max_neg.is_none() <==> (forall |j: int| 0<=j<i ==> arr@[j] >= 0),
            max_neg.is_some() ==> 
                (forall |j: int| 
                    (0<=j<i && arr@[j] < 0) ==> arr@[j] <= max_neg.unwrap()
                ) &&
                (exists |j: int| 0<=j<i && arr@[j] == max_neg.unwrap() && arr@[j] < 0),
            min_pos.is_none() <==> (forall |j: int| 0<=j<i ==> arr@[j] <= 0),
            min_pos.is_some() ==> 
                (forall |j: int| 
                    (0<=j<i && arr@[j] > 0) ==> arr@[j] >= min_pos.unwrap()
                ) &&
                (exists |j: int| 0<=j<i && arr@[j] == min_pos.unwrap() && arr@[j] > 0)
    {
        let x = arr[i];
        if x < 0 {
            if max_neg.is_none() {
                max_neg = Some(x);
            } else {
                let current = max_neg.unwrap();
                if x > current {
                    max_neg = Some(x);
                }
            }
        } else if x > 0 {
            if min_pos.is_none() {
                min_pos = Some(x);
            } else {
                let current = min_pos.unwrap();
                if x < current {
                    min_pos = Some(x);
                }
            }
        }
    }

    (max_neg, min_pos)
}
// </vc-code>

fn main() {}
}