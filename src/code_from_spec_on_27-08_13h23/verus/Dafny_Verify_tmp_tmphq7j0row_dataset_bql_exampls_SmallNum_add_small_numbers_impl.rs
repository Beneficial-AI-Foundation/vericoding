use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn add_small_numbers(a: &[i32], n: usize, max: i32) -> (r: i32)
    requires 
        n > 0,
        n <= a.len(),
        forall|i: int| 0 <= i && i < n ==> a[i] <= max,
    ensures
        r <= max * (n as i32),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn add_small_numbers(a: &[i32], n: usize, max: i32) -> (r: i32)
    requires 
        n > 0,
        n <= a.len(),
        forall|i: int| 0 <= i && i < n ==> a[i] <= max,
    ensures
        r <= max * (n as i32),
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            sum <= max * (i as i32),
    {
        sum = sum + a[i as int];
        i = i + 1;
    }
    sum
}
// </vc-code>

fn main() {
}

}