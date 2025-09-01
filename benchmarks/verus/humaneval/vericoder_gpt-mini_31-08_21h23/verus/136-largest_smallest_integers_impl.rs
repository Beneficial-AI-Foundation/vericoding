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
        invariant {
            i <= arr@.len()
            &&& (max_neg.is_none() ==> forall|j: nat| j < i ==> arr@[j as int] >= 0)
            &&& (max_neg.is_some() ==>
                    (
                        max_neg.unwrap() < 0
                        &&& exists|j: nat| j < i && arr@[j as int] == max_neg.unwrap()
                        &&& forall|k: nat| k < i && arr@[k as int] < 0 ==> arr@[k as int] <= max_neg.unwrap()
                    ))
            &&& (min_pos.is_none() ==> forall|j: nat| j < i ==> arr@[j as int] <= 0)
            &&& (min_pos.is_some() ==>
                    (
                        min_pos.unwrap() > 0
                        &&& exists|j: nat| j < i && arr@[j as int] == min_pos.unwrap()
                        &&& forall|k: nat| k < i && arr@[k as int] > 0 ==> arr@[k as int] >= min_pos.unwrap()
                    ))
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

    proof {
        // At loop exit i == arr@.len(), so invariants give the required properties.
        if max_neg.is_none() {
            assert(forall|j: nat| j < arr@.len() ==> arr@[j as int] >= 0);
        } else {
            let m = max_neg.unwrap();
            assert(m < 0);
            assert(exists|j: nat| j < arr@.len() && arr@[j as int] == m);
            assert(forall|k: nat| k < arr@.len() && arr@[k as int] < 0 ==> arr@[k as int] <= m);
        }

        if min_pos.is_none() {
            assert(forall|j: nat| j < arr@.len() ==> arr@[j as int] <= 0);
        } else {
            let p = min_pos.unwrap();
            assert(p > 0);
            assert(exists|j: nat| j < arr@.len() && arr@[j as int] == p);
            assert(forall|k: nat| k < arr@.len() && arr@[k as int] > 0 ==> arr@[k as int] >= p);
        }
    }

    (max_neg, min_pos)
}
// </vc-code>

fn main() {}
}