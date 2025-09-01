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
{
    let mut max_neg: Option<i32> = None;
    let mut min_pos: Option<i32> = None;
    let mut idx = 0;
    while idx < arr.len()
        invariant
            0 <= idx <= arr.len(),
            &&& max_neg.is_some() ==> max_neg.unwrap() < 0,
            &&& max_neg.is_some() ==> exists|j: int| 0 <= j < idx && arr@[j] == max_neg.unwrap(),
            &&& max_neg.is_some() ==> forall|j: int| #[trigger] (0 <= j < idx && arr@[j] < 0) ==> arr@[j] <= max_neg.unwrap(),
            &&& min_pos.is_some() ==> min_pos.unwrap() > 0,
            &&& min_pos.is_some() ==> exists|j: int| 0 <= j < idx && arr@[j] == min_pos.unwrap(),
            &&& min_pos.is_some() ==> forall|j: int| #[trigger] (0 <= j < idx && arr@[j] > 0) ==> arr@[j] >= min_pos.unwrap(),
    {
        let elem = arr[idx];
        if elem < 0 {
            match max_neg {
                None => {
                    max_neg = Some(elem);
                },
                Some(cur) => {
                    if elem > cur {
                        max_neg = Some(elem);
                    }
                }
            }
        } else if elem > 0 {
            match min_pos {
                None => {
                    min_pos = Some(elem);
                },
                Some(cur) => {
                    if elem < cur {
                        min_pos = Some(elem);
                    }
                }
            }
        }
        idx += 1;
    }
    (max_neg, min_pos)
}
// </vc-code>

fn main() {}
}