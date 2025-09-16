// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicates for negative and positive integers */
spec fn is_neg(x: i32) -> bool { x < 0 }
spec fn is_pos(x: i32) -> bool { x > 0 }
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
    /* code modified by LLM (iteration 5): use usize index and correct invariants to avoid spec types in runtime */
    let mut i: usize = 0;
    let mut neg: Option<i32> = Option::None;
    let mut pos: Option<i32> = Option::None;

    while i < arr.len()
        invariant
            0 <= i as int,
            i as int <= arr@.len() as int,
            neg.is_none() ==> forall|k: int| 0 <= k < i as int ==> arr@[k] >= 0,
            neg.is_some() ==> arr@.contains(neg.unwrap()) && neg.unwrap() < 0,
            neg.is_some() ==> forall|k: int| 0 <= k < i as int && arr@[k] < 0 ==> arr@[k] <= neg.unwrap(),
            pos.is_none() ==> forall|k: int| 0 <= k < i as int ==> arr@[k] <= 0,
            pos.is_some() ==> arr@.contains(pos.unwrap()) && pos.unwrap() > 0,
            pos.is_some() ==> forall|k: int| 0 <= k < i as int && arr@[k] > 0 ==> arr@[k] >= pos.unwrap(),
        decreases arr@.len() - (i as nat)
    {
        let v: i32 = arr[i];
        if v < 0 {
            match neg {
                Option::None => { neg = Option::Some(v); }
                Option::Some(curr) => {
                    if curr < v {
                        neg = Option::Some(v);
                    }
                }
            }
        } else if v > 0 {
            match pos {
                Option::None => { pos = Option::Some(v); }
                Option::Some(curr) => {
                    if v < curr {
                        pos = Option::Some(v);
                    }
                }
            }
        }
        i = i + 1;
    }

    (neg, pos)
}
// </vc-code>

}
fn main() {}