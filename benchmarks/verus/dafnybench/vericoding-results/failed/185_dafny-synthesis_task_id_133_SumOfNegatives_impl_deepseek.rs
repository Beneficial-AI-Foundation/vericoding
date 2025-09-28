use vstd::prelude::*;

verus! {

spec fn sum_negatives_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n == 0 { 
        0 
    } else if n > 0 && a[n - 1] < 0 { 
        sum_negatives_to(a, n - 1) + a[n - 1] 
    } else if n > 0 { 
        sum_negatives_to(a, n - 1) 
    } else {
        0
    }
}

// <vc-helpers>
proof fn sum_negatives_to_zero(a: &[i32])
    ensures sum_negatives_to(a, 0) == 0
{
}

proof fn sum_negatives_to_step(a: &[i32], n: int)
    requires
        0 < n <= a.len(),
    ensures
        sum_negatives_to(a, n) == sum_negatives_to(a, n - 1) + (if a[n - 1] < 0 { a[n - 1] } else { 0 })
{
}

proof fn sum_negatives_to_nonnegative_result(a: &[i32], n: int)
    requires
        0 <= n <= a.len(),
    ensures
        sum_negatives_to(a, n) <= 0
    decreases n
{
    if n > 0 {
        sum_negatives_to_nonnegative_result(a, n - 1);
        sum_negatives_to_step(a, n);
    }
}

proof fn sum_negatives_to_monotonic(a: &[i32], m: int, n: int)
    requires
        0 <= m <= n <= a.len(),
    ensures
        sum_negatives_to(a, m) >= sum_negatives_to(a, n),
    decreases n - m
{
    if m < n {
        sum_negatives_to_step(a, m + 1);
        if a[m] < 0 {
            assert(a[m] <= 0);
        }
        sum_negatives_to_monotonic(a, m + 1, n);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut result: i32 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result == sum_negatives_to(a, i as int),
            result <= 0,
        decreases a.len() - i,
    {
        let idx: usize = i;
        proof {
            sum_negatives_to_step(a, (idx + 1) as int);
        }
        let elem: i32 = a[idx];
        if elem < 0 {
            proof {
                sum_negatives_to_monotonic(a, idx as int, a.len() as int);
            }
            assert(sum_negatives_to(a, idx as int) >= sum_negatives_to(a, a.len() as int));
            assert(sum_negatives_to(a, (idx + 1) as int) == sum_negatives_to(a, idx as int) + elem);
            result = (result + elem) as i32;
            assert(result == sum_negatives_to(a, (idx + 1) as int));
        } else {
            assert(sum_negatives_to(a, (idx + 1) as int) == sum_negatives_to(a, idx as int));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}