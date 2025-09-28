use vstd::prelude::*;

verus! {

spec fn contains(v: i32, a: Seq<i32>, n: int) -> bool {
    exists|j: int| 0 <= j < n && a[j] == v
}

spec fn upper_bound(v: i32, a: Seq<i32>, n: int) -> bool {
    forall|j: int| 0 <= j < n ==> a[j] <= v
}

spec fn is_max(m: i32, a: Seq<i32>, n: int) -> bool {
    contains(m, a, n) && upper_bound(m, a, n)
}

// <vc-helpers>
proof fn lemma_max_properties(max_val: i32, max_idx: usize, a: &[i32], n: usize)
    requires 
        0 < n <= a.len(),
        max_idx < n,
        a@[max_idx as int] == max_val,
        forall|j: int| 0 <= j < n ==> a@[j] <= max_val,
    ensures is_max(max_val, a@, n as int)
{
    assert(contains(max_val, a@, n as int)) by {
        assert(0 <= max_idx < n);
        assert(a@[max_idx as int] == max_val);
    }
    assert(upper_bound(max_val, a@, n as int)) by {
        assert(forall|j: int| 0 <= j < n ==> a@[j] <= max_val);
    }
}

proof fn lemma_contains_max(max_val: i32, a: &[i32], i: usize)
    requires 
        0 < i <= a.len(),
        exists|k: int| 0 <= k < i && a@[k] == max_val,
    ensures contains(max_val, a@, i as int)
{
}
// </vc-helpers>

// <vc-spec>
fn max(a: &[i32], n: usize) -> (max: i32)
    requires 0 < n <= a.len(),
    ensures is_max(max, a@, n as int),
// </vc-spec>
// <vc-code>
{
    let mut max_val = a[0];
    let mut max_idx: usize = 0;
    let mut i = 1;
    
    while i < n
        invariant
            0 < n <= a.len(),
            1 <= i <= n,
            max_idx < i,
            a@[max_idx as int] == max_val,
            forall|j: int| 0 <= j < i ==> a@[j] <= max_val,
            contains(max_val, a@, i as int),
        decreases n - i,
    {
        if a[i] > max_val {
            max_val = a[i];
            max_idx = i;
        }
        i += 1;
    }
    
    proof {
        lemma_max_properties(max_val, max_idx, a, n);
    }
    
    max_val
}
// </vc-code>

fn main() {}

}