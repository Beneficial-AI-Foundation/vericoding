use vstd::prelude::*;

verus! {

spec fn sum_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}

// <vc-helpers>
spec fn sum_to(a: Seq<i32>, n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
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
        decreases a.len() - i
        invariant 0 <= i <= a.len()
        invariant sum == sum_to(a@, i as int)
    {
        sum += a[i];
        i += 1;
    }
    sum
}
// </vc-code>

fn main() {
}

}