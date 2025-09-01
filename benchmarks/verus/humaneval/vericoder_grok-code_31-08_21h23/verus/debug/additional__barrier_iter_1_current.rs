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
    let mut max_val = s[0];
    #[verifier::loop_isolation(false)]
    for i in 1..s.len() {
        #[verifier::loop_invariant(|@i, @max_val|
            (forall |j: int| 0 <= j < i ==> max_val >= s[j])
        )]
        if s[i] > max_val {
            max_val = s[i];
        }
    }
    proof {
        assert(forall |j: int| 0 <= j < s.len() ==> max_val >= s[j]);
        assert(exists |j: int| 0 <= j < s.len() && max_val == s[j]);
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
    let mut min_val = s[0];
    #[verifier::loop_isolation(false)]
    for i in 1..s.len() {
        #[verifier::loop_invariant(|@i, @min_val|
            (forall |j: int| 0 <= j < i ==> min_val <= s[j])
        )]
        if s[i] < min_val {
            min_val = s[i];
        }
    }
    proof {
        assert(forall |j: int| 0 <= j < s.len() ==> min_val <= s[j]);
        assert(exists |j: int| 0 <= j < s.len() && min_val == s[j]);
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
        let left_seq = arr@.subsequence(0, p + 1);
        let right_seq = arr@.subsequence(p + 1, arr.len());
        let max_left = compute_max(left_seq);
        let min_right = compute_min(right_seq);
        proof {
            assert(forall |k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr@[k] < arr@[l]);
        }
        max_left < min_right
    }
}
// </vc-code>

fn main() {}
}