use vstd::prelude::*;

verus! {

spec fn sum_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}

// <vc-helpers>
proof fn sum_to_recursive(a: &[i32], n: int)
    requires 0 <= n < a.len()
    ensures sum_to(a, n + 1) == sum_to(a, n) + a[n]
{
    reveal(sum_to);
    assert(sum_to(a, n + 1) == sum_to(a, n) + a[n]);
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &[i32]) -> (result: i32)
    ensures result == sum_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut s: i32 = 0;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            s == sum_to(a, i as int),
        decreases (a.len() as int) - (i as int)
    {
        s = s + a[i];
        proof {
            sum_to_recursive(a, i as int);
        }
        i = i + 1;
    }

    s
}
// </vc-code>

fn main() {
}

}