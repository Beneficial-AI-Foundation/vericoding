// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_negative(x: i32) -> bool { x < 0 }
spec fn is_positive(x: i32) -> bool { x > 0 }
fn max_i32(a: i32, b: i32) -> i32 { if a >= b { a } else { b } }
fn min_i32(a: i32, b: i32) -> i32 { if a <= b { a } else { b } }
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
    let mut i: usize = 0;
    let mut a_opt: Option<i32> = None; // max negative
    let mut b_opt: Option<i32> = None; // min positive

    while i < arr.len()
        invariant
            i <= arr.len(),
            (a_opt.is_none() ==> forall|j: int| 0 <= j < i as int ==> arr@[j] >= 0),
            (a_opt.is_some() ==> a_opt.unwrap() < 0),
            (a_opt.is_some() ==> exists|j: int| 0 <= j < i as int && arr@[j] == a_opt.unwrap()),
            (a_opt.is_some() ==> forall|j: int| 0 <= j < i as int && arr@[j] < 0 ==> arr@[j] <= a_opt.unwrap()),
            (b_opt.is_none() ==> forall|j: int| 0 <= j < i as int ==> arr@[j] <= 0),
            (b_opt.is_some() ==> b_opt.unwrap() > 0),
            (b_opt.is_some() ==> exists|j: int| 0 <= j < i as int && arr@[j] == b_opt.unwrap()),
            (b_opt.is_some() ==> forall|j: int| 0 <= j < i as int && arr@[j] > 0 ==> arr@[j] >= b_opt.unwrap()),
        decreases arr.len() - i
    {
        let v = arr[i];
        assert(arr@[i as int] == v);
        if v < 0 {
            match a_opt {
                None => {
                    a_opt = Some(v);
                }
                Some(a) => {
                    if v > a {
                        a_opt = Some(v);
                    }
                }
            }
        } else if v > 0 {
            match b_opt {
                None => {
                    b_opt = Some(v);
                }
                Some(b) => {
                    if v < b {
                        b_opt = Some(v);
                    }
                }
            }
        }
        i = i + 1;
    }

    (a_opt, b_opt)
}
// </vc-code>

}
fn main() {}