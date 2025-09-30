// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): corrected decreases clause in find_max_in_prefix */
fn find_max_in_prefix(v: &[i32], end: usize) -> (res: (i32, usize))
    requires
        end < v.len(),
    ensures
        0 <= res.1 <= end,
        res.0 == v[res.1 as int],
        forall|k: int| 0 <= k <= end ==> v[k] <= res.0,
{
    let mut max_val = v[0];
    let mut max_idx = 0;
    let mut i: usize = 1;
    while i <= end
        invariant
            end < v.len(),
            1 <= i <= end + 1,
            0 <= max_idx < i,
            max_val == v[max_idx as int],
            forall|k: int| 0 <= k < i ==> v[k] <= max_val,
        decreases (end + 1) - i
    {
        if v[i] > max_val {
            max_val = v[i];
            max_idx = i;
        }
        i = i + 1;
    }
    (max_val, max_idx)
}

fn find_min_in_suffix(v: &[i32], start: usize) -> (res: (i32, usize))
    requires
        start < v.len(),
    ensures
        start <= res.1 < v.len(),
        res.0 == v[res.1 as int],
        forall|k: int| start <= k < v.len() ==> v[k] >= res.0,
{
    let mut min_val = v[start];
    let mut min_idx = start;
    let mut i: usize = start + 1;
    while i < v.len()
        invariant
            start < i <= v.len(),
            start <= min_idx < i,
            min_val == v[min_idx as int],
            forall|k: int| start <= k < i ==> v[k] >= min_val,
        decreases v.len() - i
    {
        if v[i] < min_val {
            min_val = v[i];
            min_idx = i;
        }
        i = i + 1;
    }
    (min_val, min_idx)
}
// </vc-helpers>

// <vc-spec>
fn barrier(v: &[i32], p: usize) -> (b: bool)
    requires 
        v.len() > 0,
        p < v.len(),
    ensures 
        b == forall|k: usize, l: usize| 
            k <= p && p < l && l < v.len() ==> v[k as int] < v[l as int]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): no changes required, fix is in helper function */
{
    if p + 1 >= v.len() {
        assert(forall|k: usize, l: usize|
            k <= p && p < l && l < v.len() ==> v[k as int] < v[l as int]);
        return true;
    }

    let (max_left, k_max) = find_max_in_prefix(v, p);
    let (min_right, l_min) = find_min_in_suffix(v, p + 1);

    let b = max_left < min_right;
    if b {
        assert(forall|k: usize, l: usize|
            k <= p && p < l && l < v.len() ==> v[k as int] < v[l as int]);
    } else {
        assert(exists|k: usize, l: usize|
            k <= p && p < l && l < v.len() && v[k as int] >= v[l as int]
        ) by {
            assert(v[k_max as int] >= v[l_min as int]);
        };
    }
    b
}
// </vc-code>

}
fn main() {}