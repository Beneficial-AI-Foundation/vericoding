use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    sorted_a(a, a.len() as int)
}

spec fn sorted_a(a: &[int], i: int) -> bool {
    0 <= i <= a.len() && 
    forall|k: int| #![trigger a[k]] 0 < k < i ==> a[(k-1) as int] <= a[k]
}

// <vc-helpers>
proof fn sorted_a_monotonic(a: &[int], i: int, j: int)
    requires
        0 <= i <= j <= a.len(),
        sorted_a(a, j)
    ensures
        sorted_a(a, i)
{
}

proof fn sorted_a_implies_monotonic(a: &[int], i: int, k: int, l: int)
    requires
        sorted_a(a, i),
        0 <= k < l < i
    ensures
        a[k] <= a[l]
    decreases l - k
{
    if k + 1 == l {
        assert(a[k] <= a[l]);
    } else {
        sorted_a_implies_monotonic(a, i, k, l - 1);
        assert(a[k] <= a[l - 1]);
        assert(a[l - 1] <= a[l]);
    }
}
// </vc-helpers>

// <vc-spec>
fn look_for_min(a: &[int], i: usize) -> (m: usize)
    requires 
        0 <= i < a.len(),
    ensures
        i <= m < a.len(),
        forall|k: int| #![trigger a[k]] i <= k < a.len() ==> a[k] >= a[m as int],
// </vc-spec>
// <vc-code>
{
    let mut m = i;
    let mut idx = i;
    
    while idx < a.len()
        invariant
            i <= m < a.len(),
            i <= idx <= a.len(),
            forall|k: int| #![trigger a[k]] i <= k < idx ==> a[k] >= a[m as int],
        decreases (a.len() as int) - (idx as int)
    {
        if a[idx] < a[m] {
            m = idx;
        }
        idx = idx + 1;
    }
    
    proof {
        assert(idx == a.len());
        assert forall|k: int| i <= k < a.len() implies a[k] >= a[m as int] by {
            assert(k < idx);
        };
    }
    
    m
}
// </vc-code>

fn main() {
}

}