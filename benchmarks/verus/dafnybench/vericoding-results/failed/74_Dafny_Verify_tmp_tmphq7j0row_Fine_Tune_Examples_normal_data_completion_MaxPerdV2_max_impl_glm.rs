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

// </vc-helpers>

// <vc-spec>
fn max(a: &[i32], n: usize) -> (max: i32)
    requires 0 < n <= a.len(),
    ensures is_max(max, a@, n as int),
// </vc-spec>
// <vc-code>
{
    let mut max_val = a[0];
    let mut i = 1;
    while i < n
        invariant 
            1 <= i <= n,
            n <= a.len(),
            contains(max_val, a@, i as int),
            upper_bound(max_val, a@, i as int),
        decreases n - i,
    {
        assert(i < a.len());
        if a[i] > max_val {
            max_val = a[i];
        }
        i += 1;
    }
    max_val
}
// </vc-code>

fn main() {}

}