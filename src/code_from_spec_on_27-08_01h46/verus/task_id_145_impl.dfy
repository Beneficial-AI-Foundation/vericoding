use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn max_diff_spec(arr: &Vec<i32>) -> i32 {
    let max_val = seq_max(arr@);
    let min_val = seq_min(arr@);
    (max_val - min_val) as i32
}

spec fn seq_max(s: Seq<i32>) -> int
    recommends s.len() > 0
{
    seq_max_from(s, 0)
}

spec fn seq_max_from(s: Seq<i32>, start: int) -> int
    recommends 0 <= start < s.len()
    decreases s.len() - start
{
    if start + 1 >= s.len() {
        s[start] as int
    } else {
        let rest_max = seq_max_from(s, start + 1);
        if s[start] >= rest_max { s[start] as int } else { rest_max }
    }
}

spec fn seq_min(s: Seq<i32>) -> int
    recommends s.len() > 0
{
    seq_min_from(s, 0)
}

spec fn seq_min_from(s: Seq<i32>, start: int) -> int
    recommends 0 <= start < s.len()
    decreases s.len() - start
{
    if start + 1 >= s.len() {
        s[start] as int
    } else {
        let rest_min = seq_min_from(s, start + 1);
        if s[start] <= rest_min { s[start] as int } else { rest_min }
    }
}

proof fn lemma_max_min_difference(arr: &Vec<i32>)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= seq_max(arr@) - seq_min(arr@),
{
    assert forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() implies arr[i] - arr[j] <= seq_max(arr@) - seq_min(arr@) by {
        lemma_seq_max_is_max(arr@, i);
        lemma_seq_min_is_min(arr@, j);
    };
}

proof fn lemma_seq_max_is_max(s: Seq<i32>, i: int)
    requires s.len() > 0, 0 <= i < s.len()
    ensures s[i] <= seq_max(s)
    decreases s.len()
{
    lemma_seq_max_from_is_max(s, 0, i);
}

proof fn lemma_seq_max_from_is_max(s: Seq<i32>, start: int, i: int)
    requires 0 <= start < s.len(), start <= i < s.len()
    ensures s[i] <= seq_max_from(s, start)
    decreases s.len() - start
{
    if start + 1 >= s.len() {
    } else {
        if i == start {
            let rest_max = seq_max_from(s, start + 1);
            if s[start] >= rest_max {
            } else {
                if start + 1 <= i {
                    lemma_seq_max_from_is_max(s, start + 1, i);
                }
            }
        } else {
            if start + 1 <= i {
                lemma_seq_max_from_is_max(s, start + 1, i);
            }
            let rest_max = seq_max_from(s, start + 1);
            if s[start] >= rest_max {
            } else {
            }
        }
    }
}

proof fn lemma_seq_min_is_min(s: Seq<i32>, i: int)
    requires s.len() > 0, 0 <= i < s.len()
    ensures s[i] >= seq_min(s)
    decreases s.len()
{
    lemma_seq_min_from_is_min(s, 0, i);
}

proof fn lemma_seq_min_from_is_min(s: Seq<i32>, start: int, i: int)
    requires 0 <= start < s.len(), start <= i < s.len()
    ensures s[i] >= seq_min_from(s, start)
    decreases s.len() - start
{
    if start + 1 >= s.len() {
    } else {
        if i == start {
            let rest_min = seq_min_from(s, start + 1);
            if s[start] <= rest_min {
            } else {
                if start + 1 <= i {
                    lemma_seq_min_from_is_min(s, start + 1, i);
                }
            }
        } else {
            if start + 1 <= i {
                lemma_seq_min_from_is_min(s, start + 1, i);
            }
            let rest_min = seq_min_from(s, start + 1);
            if s[start] <= rest_min {
            } else {
            }
        }
    }
}

proof fn lemma_max_equals_spec_max(arr: &Vec<i32>, max_val: i32)
    requires
        arr.len() > 0,
        forall|k: int| 0 <= k < arr.len() ==> arr[k] <= max_val,
        exists|k: int| 0 <= k < arr.len() && arr[k] == max_val,
    ensures
        max_val == seq_max(arr@),
{
    lemma_max_equals_spec_max_from(arr@, 0, max_val);
}

proof fn lemma_max_equals_spec_max_from(s: Seq<i32>, start: int, max_val: i32)
    requires
        0 <= start < s.len(),
        forall|k: int| start <= k < s.len() ==> s[k] <= max_val,
        exists|k: int| start <= k < s.len() && s[k] == max_val,
    ensures
        max_val as int == seq_max_from(s, start),
    decreases s.len() - start
{
    if start + 1 >= s.len() {
        assert(s[start] == max_val);
    } else {
        let rest_max = seq_max_from(s, start + 1);
        if exists|k: int| start + 1 <= k < s.len() && s[k] == max_val {
            lemma_max_equals_spec_max_from(s, start + 1, max_val);
            if s[start] >= rest_max {
                if s[start] == max_val {
                } else {
                    assert(s[start] < max_val);
                    assert(rest_max == max_val);
                    assert(s[start] >= rest_max);
                    assert(false);
                }
            } else {
            }
        } else {
            assert(s[start] == max_val);
            if s[start] >= rest_max {
            } else {
                assert(s[start] == max_val);
                assert(forall|k: int| start + 1 <= k < s.len() ==> s[k] <= max_val);
                assert(forall|k: int| start + 1 <= k < s.len() ==> s[k] <= s[start]);
                lemma_seq_max_from_bound(s, start + 1, s[start]);
                assert(rest_max <= s[start]);
                assert(false);
            }
        }
    }
}

proof fn lemma_min_equals_spec_min(arr: &Vec<i32>, min_val: i32)
    requires
        arr.len() > 0,
        forall|k: int| 0 <= k < arr.len() ==> arr[k] >= min_val,
        exists|k: int| 0 <= k < arr.len() && arr[k] == min_val,
    ensures
        min_val == seq_min(arr@),
{
    lemma_min_equals_spec_min_from(arr@, 0, min_val);
}

proof fn lemma_min_equals_spec_min_from(s: Seq<i32>, start: int, min_val: i32)
    requires
        0 <= start < s.len(),
        forall|k: int| start <= k < s.len() ==> s[k] >= min_val,
        exists|k: int| start <= k < s.len() && s[k] == min_val,
    ensures
        min_val as int == seq_min_from(s, start),
    decreases s.len() - start
{
    if start + 1 >= s.len() {
        assert(s[start] == min_val);
    } else {
        let rest_min = seq_min_from(s, start + 1);
        if exists|k: int| start + 1 <= k < s.len() && s[k] == min_val {
            lemma_min_equals_spec_min_from(s, start + 1, min_val);
            if s[start] <= rest_min {
                if s[start] == min_val {
                } else {
                    assert(s[start] > min_val);
                    assert(rest_min == min_val);
                    assert(s[start] <= rest_min);
                    assert(false);
                }
            } else {
            }
        } else {
            assert(s[start] == min_val);
            if s[start] <= rest_min {
            } else {
                assert(s[start] == min_val);
                assert(forall|k: int| start + 1 <= k < s.len() ==> s[k] >= min_val);
                assert(forall|k: int| start + 1 <= k < s.len() ==> s[k] >= s[start]);
                lemma_seq_min_from_bound(s, start + 1, s[start]);
                assert(rest_min >= s[start]);
                assert(false);
            }
        }
    }
}

proof fn lemma_seq_max_from_bound(s: Seq<i32>, start: int, bound: i32)
    requires 
        0 <= start < s.len(),
        forall|k: int| start <= k < s.len() ==> s[k] <= bound
    ensures
        seq_max_from(s, start) <= bound
    decreases s.len() - start
{
    if start + 1 >= s.len() {
    } else {
        lemma_seq_max_from_bound(s, start + 1, bound);
    }
}

proof fn lemma_seq_min_from_bound(s: Seq<i32>, start: int, bound: i32)
    requires 
        0 <= start < s.len(),
        forall|k: int| start <= k < s.len() ==> s[k] >= bound
    ensures
        seq_min_from(s, start) >= bound
    decreases s.len() - start
{
    if start + 1 >= s.len() {
    } else {
        lemma_seq_min_from_bound(s, start + 1, bound);
    }
}
// </vc-helpers>

// <vc-spec>
fn max_difference(arr: &Vec<i32>) -> (diff: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    for i in 1..arr.len()
        invariant
            0 < i <= arr.len(),
            forall|k: int| 0 <= k < i ==> arr[k] <= max_val,
            forall|k: int| 0 <= k < i ==> arr[k] >= min_val,
            exists|k: int| 0 <= k < i && arr[k] == max_val,
            exists|k: int| 0 <= k < i && arr[k] == min_val,
    {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
    }
    
    proof {
        lemma_max_equals_spec_max(arr, max_val);
        lemma_min_equals_spec_min(arr, min_val);
        lemma_max_min_difference(arr);
    }
    
    max_val - min_val
}
// </vc-code>

} // verus!

fn main() {}