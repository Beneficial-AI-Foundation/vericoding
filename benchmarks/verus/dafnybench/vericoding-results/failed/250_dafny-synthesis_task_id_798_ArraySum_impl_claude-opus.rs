use vstd::prelude::*;

verus! {

spec fn sum_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}

// <vc-helpers>
proof fn sum_to_lemma(a: &[i32], n: int)
    requires 0 <= n < a.len()
    ensures sum_to(a, n + 1) == sum_to(a, n) + a[n]
    decreases n
{
    // The ensures clause follows directly from the definition of sum_to
    // when n + 1 > 0, which is guaranteed by our requires clause
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
        decreases a.len() - i,
    {
        proof {
            sum_to_lemma(a, i as int);
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