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
proof fn lemma_contains_max(v: i32, a: Seq<i32>, n: int, max_val: i32)
    requires
        0 < n,
        contains(max_val, a, n),
        upper_bound(max_val, a, n),
    ensures
        is_max(max_val, a, n),
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn max(a: &[i32], n: usize) -> (max: i32)
    requires 0 < n <= a.len(),
    ensures is_max(max, a@, n as int),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn max(a: &[i32], n: usize) -> (max: i32)
    requires
        0 < n <= a.len(),
    ensures
        is_max(max, a@, n as int),
{
    let mut max_val = a[0];
    let mut i: usize = 1;

    while i < n
        invariant
            0 < n <= a.len(),
            1 <= i <= n,
            contains(max_val, a@, i as int),
            upper_bound(max_val, a@, i as int),
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i = i + 1;
    }

    proof {
        lemma_contains_max(max_val, a@, n as int, max_val);
    }

    max_val
}
// </vc-code>

fn main() {}

}