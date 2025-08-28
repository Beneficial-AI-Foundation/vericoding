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
    s >= 0 && t >= s && t <= a.len()
}

proof fn sum_empty(a: Seq<i32>, s: int)
    ensures sum(a, s, s) == 0
{
}

proof fn sum_extend(a: Seq<i32>, s: int, t: int)
    requires sum_nonneg(a, s, t + 1), t >= 0, s <= t
    ensures sum(a, s, t + 1) == sum(a, s, t) + a[t]
    decreases t - s
{
    if s < 0 || s >= t + 1 || t + 1 > a.len() {
    } else if s == t {
        assert(sum(a, s, t) == 0);
    } else {
        sum_extend(a, s, t - 1);
        assert(sum(a, s, t) == a[t - 1] + sum(a, s, t - 1));
        assert(sum(a, s, t + 1) == a[t] + sum(a, s, t));
        assert(sum(a, s, t + 1) == a[t] + a[t - 1] + sum(a, s, t - 1));
        assert(sum(a, s, t + 1) == sum(a, s, t) + a[t]);
    }
}

proof fn sum_bounds_helper(a: Seq<i32>, s: int, t: int, max_i: int, max_j: int, max_sum: int)
    requires 
        sum_nonneg(a, s, t),
        sum_nonneg(a, max_i, max_j),
        sum(a, max_i, max_j) == max_sum,
        forall|k: int, l: int| 0 <= k <= l < t ==> sum(a, k, l) <= max_sum
    ensures
        sum(a, s, t) <= max_sum || (exists|k: int, l: int| 0 <= k <= l <= t && sum(a, k, l) > max_sum)
{
}

proof fn sum_inductive(a: Seq<i32>, i: int, j: int)
    requires 0 <= i <= j < a.len()
    ensures sum(a, i, j + 1) == sum(a, i, j) + a[j]
{
    sum_extend(a, i, j);
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
    let mut max_i: usize = 0;
    let mut max_j: usize = 0;
    let mut max_sum: i64 = 0;
    
    let mut i: usize = 0;
    
    while i <= a.len()
        invariant
            i <= a.len(),
            max_i <= max_j <= a.len(),
            forall|k: int, l: int| 0 <= k <= l <= i ==> sum(a@, k, l) <= sum(a@, max_i as int, max_j as int)
        decreases a.len() - i
    {
        let mut j: usize = i;
        let mut current_sum: i64 = 0;
        
        while j < a.len()
            invariant
                i <= j <= a.len(),
                max_i <= max_j <= a.len(),
                current_sum == sum(a@, i as int, j as int),
                forall|k: int, l: int| 0 <= k <= l <= i ==> sum(a@, k, l) <= sum(a@, max_i as int, max_j as int),
                forall|l: int| i <= l <= j ==> sum(a@, i as int, l) <= sum(a@, max_i as int, max_j as int)
            decreases a.len() - j
        {
            if current_sum > max_sum {
                max_i = i;
                max_j = j;
                max_sum = current_sum;
            }
            
            proof {
                sum_inductive(a@, i as int, j as int);
            }
            current_sum = add(current_sum, a[j]);
            j += 1;
        }
        
        if current_sum > max_sum {
            max_i = i;
            max_j = j;
            max_sum = current_sum;
        }
        
        i += 1;
    }
    
    (max_i, max_j)
}
// </vc-code>

fn main() {}
}