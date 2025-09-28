use vstd::prelude::*;

verus! {

spec fn sum_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}

// <vc-helpers>
spec fn sum_to_seq(a: Seq<i32>, n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to_seq(a, n - 1) + a[n - 1] }
}

proof fn sum_to_step(a: &[i32], n: int)
    requires 0 <= n <= a.len()
    ensures sum_to(a, n) == sum_to(a, n - 1) + (if n > 0 { a[n - 1] } else { 0 })
{
    if n <= 0 {
        assert(sum_to(a, n) == 0);
        assert(sum_to(a, n - 1) == 0);
    } else {
        assert(sum_to(a, n) == sum_to(a, n - 1) + a[n - 1]);
    }
}

proof fn sum_to_monotonic(a: &[i32], i: int, j: int)
    requires 0 <= i <= j <= a.len()
    ensures sum_to(a, i) + sum_to_seq(a@.subrange(i, j), j - i) == sum_to(a, j)
    decreases j - i
{
    if i == j {
        assert(sum_to_seq(a@.subrange(i, j), 0) == 0);
    } else {
        sum_to_monotonic(a, i, j - 1);
        assert(a@.subrange(i, j - 1) =~= a@.subrange(i, j).subrange(0, (j - 1) - i));
    }
}

proof fn sum_to_add_one(a: &[i32], n: int)
    requires 0 <= n < a.len()
    ensures sum_to(a, n + 1) == sum_to(a, n) + a[n]
{
    assert(sum_to(a, n + 1) == sum_to(a, n) + a[n]);
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &[i32]) -> (result: i32)
    ensures result == sum_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            sum == sum_to(a, i as int),
            if sum >= 0 { sum } else { -sum } <= i * 2147483647
        decreases a.len() - i
    {
        proof {
            sum_to_add_one(a, i as int);
            assert(sum_to(a, (i + 1) as int) == sum_to(a, i as int) + a[i as int]);
            let abs_ai = if a[i as int] >= 0 { a[i as int] } else { -a[i as int] };
            assert(abs_ai <= 2147483647);
            let abs_sum = if sum >= 0 { sum } else { -sum };
            let abs_new_sum = if (sum + a[i as int]) >= 0 { sum + a[i as int] } else { -(sum + a[i as int]) };
            assert(abs_new_sum <= abs_sum + abs_ai);
        }
        
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}
// </vc-code>

fn main() {
}

}