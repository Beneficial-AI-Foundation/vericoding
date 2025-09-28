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
    let mut sum = 0;
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            i <= a.len(),
            sum <= max * (i as i32),
        decreases n - i
    {
        assert(i < n);
        assert(i < a.len());
        proof {
            assert(a[i as int] <= max);
            assert(sum + a[i as int] <= max * (i as i32) + max);
            assert(max * (i as i32) + max == max * ((i + 1) as i32));
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