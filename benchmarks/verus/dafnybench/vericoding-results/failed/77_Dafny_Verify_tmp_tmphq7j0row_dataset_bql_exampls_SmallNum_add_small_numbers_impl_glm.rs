use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add_small_numbers(a: &[i32], n: usize, max: i32) -> (r: i32)
    requires 
        n > 0,
        n <= a.len(),
        forall|i: int| 0 <= i && i < n ==> a[i] <= max,
    ensures
        r <= max * (n as i32),
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    for i in 0..n
        invariant
            0 <= i <= n,
            n <= a.len(),
            i <= a.len(),
            sum <= max * (i as i32),
    {
        assert(i < a.len());
        assert(a[i] <= max);
        proof {
            assert(sum <= max * (i as i32) + a[i]);
            assert(sum <= max * (i as i32) + max);
            assert(sum <= max * ((i as i32) + 1));
        }
        sum = sum + a[i];
    }
    sum
}
// </vc-code>

fn main() {
}

}