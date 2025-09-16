// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 4): Fix termination by changing decreases to arr.len() for largest_neg and smallest_pos */
/* spec fn largest_neg(arr: Seq<i32>) -> Option<i32>
    decreases arr.len()
{
    if arr.len() == 0 {
        None
    } else {
        let rest = largest_neg(arr.drop_last());
        let x = arr.last();
        if x >= 0 {
            rest
        } else {
            match rest {
                None => Some(x),
                Some(y) => if x > y { Some(x) } else { Some(y) }
            }
        }
    }
}
*/

/* spec fn smallest_pos(arr: Seq<i32>) -> Option<i32>
    decreases arr.len()
{
    if arr.len() == 0 {
        None
    } else {
        let rest = smallest_pos(arr.drop_last());
        let x = arr.last();
        if x <= 0 {
            rest
        } else {
            match rest {
                None => Some(x),
                Some(y) => if x < y { Some(x) } else { Some(y) }
            }
        }
    }
}
*/

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
    /* code modified by LLM (iteration 4): Implement loop to compute largest negative and smallest positive integers */
    let mut max_neg: Option<i32> = None;
    let mut min_pos: Option<i32> = None;
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            max_neg.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] >= 0,
            max_neg.is_some() ==> (forall|j: int| 0 <= j < i && arr@[j] < 0 ==> arr@[j] <= max_neg.unwrap()) && arr@.contains(max_neg.unwrap()) && max_neg.unwrap() < 0,
            min_pos.is_none() ==> forall|j: int| 0 <= j < i ==> arr@[j] <= 0,
            min_pos.is_some() ==> (forall|j: int| 0 <= j < i && arr@[j] > 0 ==> arr@[j] >= min_pos.unwrap()) && arr@.contains(min_pos.unwrap()) && min_pos.unwrap() > 0,
        decreases arr.len() - i
    {
        let x = arr[i];
        if x < 0 {
            if max_neg.is_none() || x > max_neg.unwrap() {
                max_neg = Some(x);
            }
        }
        if x > 0 {
            if min_pos.is_none() || x < min_pos.unwrap() {
                min_pos = Some(x);
            }
        }
        i = i + 1;
    }
    (max_neg, min_pos)
}

// </vc-code>

}
fn main() {}