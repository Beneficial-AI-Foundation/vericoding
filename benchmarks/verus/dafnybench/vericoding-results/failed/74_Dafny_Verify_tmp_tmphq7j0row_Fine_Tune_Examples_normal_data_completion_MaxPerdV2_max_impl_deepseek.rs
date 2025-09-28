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
proof lemma_max_exists(a: Seq<i32>, n: int)
    requires
        0 < n <= a.len(),
    ensures
        exists|m: i32| is_max(m, a, n),
{
    let mut i: int = 0;
    let mut current_max = a[0];
    
    while i < n
        invariant
            0 <= i <= n,
            contains(current_max, a, i),
            upper_bound(current_max, a, i),
    {
        if a[i] > current_max {
            current_max = a[i];
        }
        i = i + 1;
    }
    
    assert(is_max(current_max, a, n));
}

proof lemma_upper_bound_transitive(v1: i32, v2: i32, a: Seq<i32>, n: int)
    requires
        upper_bound(v1, a, n),
        v2 <= v1,
    ensures
        upper_bound(v2, a, n),
{
}

proof lemma_contains_preserved(v: i32, a: Seq<i32>, n: int, m: int)
    requires
        0 <= n <= m <= a.len(),
        contains(v, a, n),
    ensures
        contains(v, a, m),
{
}

proof lemma_upper_bound_extends(v: i32, a: Seq<i32>, n: int)
    requires
        0 <= n < a.len(),
        upper_bound(v, a, n),
        v >= a[n],
    ensures
        upper_bound(v, a, n + 1),
{
    assert forall|j: int| 0 <= j < n + 1 implies a[j] <= v by {
        if j < n {
            assert(a[j] <= v);
        } else {
            assert(j == n);
            assert(a[j] <= v);
        }
    };
}

proof lemma_contains_extends(v: i32, a: Seq<i32>, n: int)
    requires
        0 <= n < a.len(),
        (v == a[n] || contains(v, a, n)),
    ensures
        contains(v, a, n + 1),
{
    if v == a[n] {
        assert(exists|j: int| 0 <= j < n + 1 && a[j] == v by {
            assert(a[n] == v);
        });
    } else {
        assert(exists|j: int| 0 <= j < n && a[j] == v);
        assert(exists|j: int| 0 <= j < n + 1 && a[j] == v);
    }
}
// </vc-helpers>

// <vc-spec>
fn max(a: &[i32], n: usize) -> (max: i32)
    requires 0 < n <= a.len(),
    ensures is_max(max, a@, n as int),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 1;
    let mut max_val = a[0];
    
    while i < n
        invariant
            1 <= i <= n,
            is_max(max_val, a@, i as int),
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        proof {
            if a[i] > max_val {
                assert(contains(a[i], a@, (i as int) + 1) by {
                    lemma_contains_extends(a[i], a@, i as int);
                });
                assert(upper_bound(a[i], a@, (i as int) + 1) by {
                    lemma_upper_bound_extends(a[i], a@, i as int, a[i] >= a[i]);
                    assert forall|j: int| 0 <= j <= i as int implies a@[j] <= a[i] by {
                        if j < i as int {
                            assert(a@[j] <= max_val);
                            assert(max_val < a[i]);
                        } else if j == i as int {
                            assert(a@[j] == a[i]);
                        }
                    };
                });
                assert(is_max(a[i], a@, (i as int) + 1));
            } else {
                assert(contains(max_val, a@, (i as int) + 1) by {
                    lemma_contains_extends(max_val, a@, i as int);
                });
                assert(upper_bound(max_val, a@, (i as int) + 1) by {
                    lemma_upper_bound_extends(max_val, a@, i as int, a[i] <= max_val);
                });
                assert(is_max(max_val, a@, (i as int) + 1));
            }
        }
        i = i + 1;
    }
    
    max_val
}
// </vc-code>

fn main() {}

}