use vstd::prelude::*;

verus! {

spec fn sum_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}

// <vc-helpers>
proof fn sum_to_step(a: &[i32], i: int)
    requires 0 <= i < a.len()
    ensures sum_to(a, i + 1) == sum_to(a, i) + a[i]
{
    assert(i + 1 > 0);
    assert(sum_to(a, i + 1)
        == if i + 1 <= 0 { 0 } else { sum_to(a, (i + 1) - 1) + a[(i + 1) - 1] });
    assert((i + 1) - 1 == i);
    assert(sum_to(a, i + 1) == sum_to(a, i) + a[i]);
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
            0 <= i as int <= a.len() as int,
            (sum as int) == sum_to(a, i as int)
    {
        let ai = a[i];
        let old_sum = sum;
        let old_i = i;

        sum = sum + ai;
        i = i + 1;

        proof {
            assert(0 <= old_i as int);
            assert(old_i as int < a.len() as int);
            sum_to_step(a, old_i as int);
            assert(i as int == old_i as int + 1);
            assert((sum as int) == (old_sum as int) + (ai as int));
            assert(sum_to(a, i as int) == sum_to(a, old_i as int) + a[old_i as int]);
            assert((sum as int) == sum_to(a, i as int));
        }
    }
    assert((sum as int) == sum_to(a, a.len() as int));
    sum
}
// </vc-code>

fn main() {
}

}