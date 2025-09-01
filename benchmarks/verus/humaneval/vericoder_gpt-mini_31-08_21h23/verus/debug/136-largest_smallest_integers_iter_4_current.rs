use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let mut i: nat = 0;
    let mut max_neg: Option<i32> = None;
    let mut min_pos: Option<i32> = None;

    while i < arr@.len()
        invariant { i <= arr@.len() }
        invariant { max_neg.is_none() ==> forall|j: nat| j < i ==> arr@[j as int] >= 0 }
        invariant {
            max_neg.is_some() ==>
            (
                let m = max_neg.unwrap();
                &&& m < 0
                &&& exists|j: nat| j < i && arr@[j as int] == m
                &&& forall|k: nat| k < i && arr@[k as int] < 0 ==> arr@[k as int] <= m
            )
        }
        invariant { min_pos.is_none() ==> forall|j: nat| j < i ==> arr@[j as int] <= 0 }
        invariant {
            min_pos.is_some() ==>
            (
                let p = min_pos.unwrap();
                &&& p > 0
                &&& exists|j: nat| j < i && arr@[j as int] == p
                &&& forall|k: nat| k < i && arr@[k as int] > 0 ==> arr@[k as int] >= p
            )
        }
        decreases { arr@.len() - i }
    {
        let x: i32 = arr@[i as int];

        if x < 0 {
            match max_neg {
                Some(m) => {
                    if x > m {
                        max_neg = Some(x);
                    }
                }
                None => {
                    max_neg = Some(x);
                }
            }
        }

        if x > 0 {
            match min_pos {
                Some(p) => {
                    if x < p {
                        min_pos = Some(x);
                    }
                }
                None => {
                    min_pos = Some(x);
                }
            }
        }

        i += 1;
    }

    (max_neg, min_pos)
}
// </vc-code>

fn main() {}
}