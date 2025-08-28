#![crate_name = "max_segment_sum"]

use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<i32>, s: int, t: int) -> int
    decreases t - s,
{
    if s < 0 || s >= t || t > a.len() {
        0
    } else {
        a[t - 1] + sum(a, s, t - 1)
    }
}

// <vc-helpers>
#[verifier::external_body]
fn add(a: i64, b: i32) -> (result: i64)
    ensures
        result == a + b,
{
    a + b as i64
}

spec fn sum_nonneg(a: Seq<i32>, s: int, t: int) -> bool {
    0 <= s <= t <= a.len()
}

proof fn sum_monotonic(a: Seq<i32>, s: int, t1: int, t2: int)
    requires
        sum_nonneg(a, s, t1),
        sum_nonneg(a, s, t2),
        t1 <= t2,
    ensures
        sum(a, s, t1) + sum(a, t1, t2) == sum(a, s, t2),
    decreases t2 - t1,
{
    if t1 == t2 {
    } else {
        sum_monotonic(a, s, t1, t2 - 1);
    }
}

proof fn sum_empty(a: Seq<i32>, s: int)
    ensures
        sum(a, s, s) == 0,
{
}

proof fn sum_bounds_helper(a: Seq<i32>, k: int, l: int, i: int)
    requires
        0 <= k <= l <= i + 1,
        a.len() > 0,
        i < a.len(),
        forall|k2: int, l2: int| 0 <= k2 <= l2 <= i ==> sum(a, k2, l2) <= 0,
    ensures
        sum(a, k, l) <= sum(a, 0, 0),
{
    if k <= l <= i {
        assert(sum(a, k, l) <= 0);
        assert(sum(a, 0, 0) == 0);
    } else if k <= i < l {
        sum_monotonic(a, k, i, l);
        assert(sum(a, k, i) <= 0);
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_segment_sum(a: &Vec<i32>, s: usize, t: usize) -> (p: (usize, usize)) by (nonlinear_arith)
    ensures
        ({ let (i, j) = p; 0 <= i <= j <= a.len() }),
        ({ let (i, j) = p; forall|k: int, l: int| 0 <= k <= l <= a.len() ==> sum(a@, k, l) <= sum(a@, i as int, j as int) })
// </vc-spec>

// <vc-code>
{
    let mut best_i = 0usize;
    let mut best_j = 0usize;
    let mut best_sum = 0i64;
    
    let mut i = 0usize;
    while i < a.len()
        invariant
            i <= a.len(),
            best_i <= best_j <= a.len(),
            best_sum == sum(a@, best_i as int, best_j as int),
            forall|k: int, l: int| 0 <= k <= l <= i ==> sum(a@, k, l) <= best_sum,
        decreases a.len() - i,
    {
        let mut j = i;
        let mut curr_sum = 0i64;
        while j < a.len()
            invariant
                i <= j <= a.len(),
                best_i <= best_j <= a.len(),
                best_sum == sum(a@, best_i as int, best_j as int),
                curr_sum == sum(a@, i as int, j as int),
                forall|k: int, l: int| 0 <= k <= l <= i ==> sum(a@, k, l) <= best_sum,
                forall|l: int| i <= l < j ==> sum(a@, i as int, l) <= best_sum,
            decreases a.len() - j,
        {
            if curr_sum > best_sum {
                best_i = i;
                best_j = j;
                best_sum = curr_sum;
            }
            curr_sum = add(curr_sum, a[j]);
            j += 1;
        }
        if curr_sum > best_sum {
            best_i = i;
            best_j = j;
            best_sum = curr_sum;
        }
        
        proof {
            let old_best_sum = best_sum;
            assert(forall|k: int, l: int| 0 <= k <= l <= i ==> sum(a@, k, l) <= old_best_sum);
            assert(forall|l: int| i <= l <= j ==> sum(a@, i as int, l) <= best_sum);
            
            assert(forall|k: int, l: int| 0 <= k <= l <= i + 1 implies sum(a@, k, l) <= best_sum) by {
                if k <= l <= i {
                    assert(sum(a@, k, l) <= old_best_sum);
                    assert(old_best_sum <= best_sum);
                } else if k == i + 1 {
                    sum_empty(a@, k);
                    assert(sum(a@, k, l) == 0);
                    assert(0 <= best_sum);
                } else if k <= i < l <= i + 1 {
                    if k == i && l == i + 1 {
                        assert(sum(a@, i as int, l) <= best_sum);
                    } else {
                        assert(k <= l <= i);
                        assert(sum(a@, k, l) <= old_best_sum);
                        assert(old_best_sum <= best_sum);
                    }
                }
            };
        }
        
        i += 1;
    }
    (best_i, best_j)
}
// </vc-code>

fn main() {}
}