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
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn max(a: &[i32], n: usize) -> (max: i32)
    requires 0 < n <= a.len(),
    ensures is_max(max, a@, n as int),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 1usize;
    let mut idx: usize = 0usize;
    let mut m: i32 = a[0];

    while i < n
        invariant i <= n && idx < i && m == a@[(idx as int)] && forall|k: int| 0 <= k && k < (i as int) ==> a@[k] <= m;
    {
        let ai: i32 = a[i];
        if ai > m {
            m = ai;
            idx = i;
        }
        i = i + 1;
    }

    proof {
        // At loop exit, i >= n and by invariant i <= n, hence i == n
        assert(!(i < n));
        assert(i >= n);
        assert(i <= n);
        assert(i == n);
        // From the invariant with i == n, we get upper_bound
        assert(forall|k: int| 0 <= k && k < (n as int) ==> a@[k] <= m);
        // And we have idx < n and m == a@[idx], giving contains
        assert(idx < i);
        assert(idx < n);
        assert(m == a@[(idx as int)]);
    }

    m
}
// </vc-code>

fn main() {}

}