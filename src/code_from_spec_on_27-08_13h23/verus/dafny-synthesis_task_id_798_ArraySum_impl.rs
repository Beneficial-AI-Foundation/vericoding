use vstd::prelude::*;

verus! {

spec fn sum_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}

// <vc-helpers>
spec fn sum_to_prefix(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to_prefix(a, n - 1) + a[n - 1] }
}

proof fn sum_to_prefix_correct(a: &[i32], n: int)
    requires 0 <= n <= a.len()
    ensures sum_to_prefix(a, n) == sum_to(a, n)
    decreases n
{
    if n <= 0 {
        assert(sum_to_prefix(a, 0) == 0);
        assert(sum_to(a, 0) == 0);
    } else {
        sum_to_prefix_correct(a, n - 1);
        assert(sum_to_prefix(a, n) == sum_to_prefix(a, n - 1) + a[n - 1]);
        assert(sum_to(a, n) == sum_to(a, n - 1) + a[n - 1]);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn array_sum(a: &[i32]) -> (result: i32)
    ensures result == sum_to(a, a.len() as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn array_sum(a: &[i32]) -> (result: i32)
    ensures result == sum_to(a, a.len() as int)
{
    let mut sum = 0;
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == sum_to(a, i as int)
    {
        sum = sum + a[i];
        i = i + 1;
    }
    proof {
        sum_to_prefix_correct(a, a.len() as int);
    }
    sum
}
// </vc-code>

fn main() {
}

}