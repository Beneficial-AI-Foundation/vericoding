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

spec fn sum_is_monotonic(a: Seq<i32>, s: int, t: int) -> bool {
    forall|i: int, j: int| s <= i <= j <= t ==> sum(a, s, i) <= sum(a, s, j)
}

proof fn sum_empty(a: Seq<i32>, s: int)
    ensures sum(a, s, s) == 0
{
}

proof fn sum_extend(a: Seq<i32>, s: int, t: int)
    requires 0 <= s <= t < a.len()
    ensures sum(a, s, t + 1) == sum(a, s, t) + a[t]
    decreases t - s
{
    if s == t {
        assert(sum(a, s, t) == 0);
        assert(sum(a, s, t + 1) == a[t] + sum(a, s, t));
    } else {
        sum_extend(a, s, t - 1);
    }
}

proof fn sum_invariant_helper(a: Seq<i32>, i: int, j: int, best_i: int, best_j: int)
    requires
        0 <= i < j <= a.len(),
        0 <= best_i <= best_j <= a.len(),
        forall|k: int, l: int| 0 <= k <= l <= i ==> sum(a, k, l) <= sum(a, best_i, best_j),
        forall|l: int| i <= l <= j ==> sum(a, i, l) <= sum(a, best_i, best_j)
    ensures
        forall|k: int, l: int| 0 <= k <= l <= i + 1 ==> sum(a, k, l) <= sum(a, best_i, best_j)
{
    assert forall|k: int, l: int| 0 <= k <= l <= i + 1 implies sum(a, k, l) <= sum(a, best_i, best_j) by {
        if l <= i {
            assert(sum(a, k, l) <= sum(a, best_i, best_j));
        } else {
            assert(k <= i + 1 && l <= i + 1);
            if k <= i {
                assert(sum(a, k, l) <= sum(a, best_i, best_j));
            } else {
                assert(k == i + 1 && l == i + 1);
                assert(sum(a, k, l) == 0);
                assert(sum(a, k, l) <= sum(a, best_i, best_j));
            }
        }
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
    let mut max_sum = 0i64;
    let mut best_i = 0usize;
    let mut best_j = 0usize;
    
    let mut i = 0usize;
    while i < a.len()
        invariant
            i <= a.len(),
            best_i <= best_j <= a.len(),
            forall|k: int, l: int| 0 <= k <= l <= i ==> sum(a@, k, l) <= sum(a@, best_i as int, best_j as int)
        decreases a.len() - i
    {
        let mut j = i;
        let mut current_sum = 0i64;
        
        while j < a.len()
            invariant
                i <= j <= a.len(),
                best_i <= best_j <= a.len(),
                forall|k: int, l: int| 0 <= k <= l <= i ==> sum(a@, k, l) <= sum(a@, best_i as int, best_j as int),
                forall|l: int| i <= l <= j ==> sum(a@, i as int, l) <= sum(a@, best_i as int, best_j as int)
            decreases a.len() - j
        {
            if current_sum >= max_sum {
                max_sum = current_sum;
                best_i = i;
                best_j = j;
            }
            
            current_sum = add(current_sum, a[j]);
            j += 1;
        }
        
        if current_sum >= max_sum {
            max_sum = current_sum;
            best_i = i;
            best_j = j;
        }
        
        proof {
            if i + 1 < a.len() {
                sum_invariant_helper(a@, i as int, j as int, best_i as int, best_j as int);
            }
        }
        
        i += 1;
    }
    
    (best_i, best_j)
}
// </vc-code>

fn main() {}
}