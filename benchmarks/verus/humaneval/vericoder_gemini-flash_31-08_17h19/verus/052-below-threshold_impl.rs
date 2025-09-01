use vstd::prelude::*;

verus! {

// <vc-helpers>
fn for_all_below_threshold(l: &[i32], t: i32) -> (result: bool) {
    if l.len() == 0 {
        return true;
    }
    let mut i = 0;
    while i < l.len()
        invariant
            0 <= i && i <= l.len(),
            forall|j: int| 0 <= j < i ==> l[j] < t,
    {
        if l[i as usize] >= t {
            return false;
        }
        i = i + 1;
    }
    true
}

fn for_all_below_threshold_recursive(l: &[i32], t: i32) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i as int] < t,
{
    if l.len() == 0 {
        true
    } else {
        if l[0] >= t {
            false
        } else {
            // Need to create a sub-slice for recursive call
            // Using l.subslice(start, end) for Verus-compatible slicing
            let sub_slice = l.subslice(1, l.len());
            for_all_below_threshold_recursive(sub_slice, t)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn below_threshold(l: &[i32], t: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    below_threshold_recursive(l, t)
    // impl-end
}

fn below_threshold_recursive(l: &[i32], t: i32) -> (result: bool)
    ensures
        result == for_all_below_threshold_recursive(l, t),
{
    if l.len() == 0 {
        true
    } else {
        if l[0] >= t {
            false
        } else {
            let sub_slice = l.subslice(1, l.len());
            below_threshold_recursive(sub_slice, t)
        }
    }
}
// </vc-code>

fn main() {}
}