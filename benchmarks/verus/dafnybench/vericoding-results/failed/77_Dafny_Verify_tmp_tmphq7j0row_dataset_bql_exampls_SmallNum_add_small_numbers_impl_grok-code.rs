use vstd::prelude::*;

verus! {

// <vc-helpers>
//
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
	let mut sum = 0i32;
	let mut i = 0usize;
	proof {
		assert(forall|i: int| 0 <= i && i < n ==> a[i] <= max);
	}
	while i < n
		invariant
			i <= n,
			i <= a.len(),
			sum <= max * (i as i32),
		decreases n - i,
	{
		sum = sum + a[i];
		i = i + 1usize;
	}
	sum
}
// </vc-code>

fn main() {
}

}