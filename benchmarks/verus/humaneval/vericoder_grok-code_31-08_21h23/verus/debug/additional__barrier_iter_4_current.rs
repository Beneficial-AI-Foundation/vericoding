use vstd::prelude::*;

verus! {

// <vc-helpers>
fn compute_max(s: Seq<i32>) -> (r: i32)
    requires
        s.len() > 0,
    ensures
        (forall|i: int| 0 <= i < s.len() ==> r >= s[i]) &&
        (exists|j: int| 0 <= j < s.len() && r == s[j]),
{
    let mut max_val = s.index(0);
    let mut i: usize = 1;
    #[verifier::loop_isolation(false)]
    while i < (s.len() as usize)
        invariant
            (forall |j: int| 0 <= j < (i as int) ==> max_val >= s.index(j))
            decreases arr@.len() - (i as int),
    {
        if s.index(i as int) > max_val {
            max_val = s.index(i as int);
        }
        i = i + 1;
    }
    max_val
}

fn compute_min(s: Seq<i32>) -> (r: i32)
    requires
        s.len() > 0,
    ensures
        (forall|i: int| 0 <= i < s.len() ==> r <= s[i]) &&
        (exists|j: int| 0 <= j < s.len() && r == s[j]),
{
    let mut min_val = s.index(0);
    let mut i: usize = 1;
    #[verifier::loop_isolation(false)]
    while i < (s.len() as usize)
        invariant
            (forall |j: int| 0 <= j < (i as int) ==> min_val <= s.index(j))
            decreases arr@.len() - (i as int),
    {
        if s.index(i as int) < min_val {
            min_val = s.index(i as int);
        }
        i = i + 1;
    }
    min_val
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if p + 1 >= arr.len() {
        true
    } else {
        let left_seq = arr@.subrange(0, (p as int) + 1);
        let right_seq = arr@.subrange((p as int) + 1, arr@.len());
        let max_left = compute_max(left_seq);
        let min_right = compute_min(right_seq);
        max_left < min_right
    }
}
// </vc-code>

fn main() {}
}