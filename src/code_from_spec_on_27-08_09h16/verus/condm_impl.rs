use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn safe_add(x: i32) -> i32 {
    if x == i32::MAX { i32::MIN } else { x + 1 }
}

proof fn safe_add_preserves_parity(x: i32)
    ensures safe_add(x) % 2 != x % 2
{
    if x == i32::MAX {
        assert(safe_add(x) == i32::MIN);
        assert(i32::MIN % 2 == 0);
        assert(i32::MAX % 2 == 1);
    } else {
        assert(safe_add(x) == x + 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, N: u32)
		// pre-conditions-start
		requires
			N > 0,
			old(a).len() == N,
		// pre-conditions-end
		// post-conditions-start
		ensures
			forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
		// post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            forall |k: int| 0 <= k < i ==> a[k] % 2 == N % 2,
        decreases a.len() - i,
    {
        if a[i] % 2 != N % 2 {
            if N % 2 == 0 {
                if a[i] % 2 == 1 {
                    let val = a[i];
                    a.set(i, safe_add(val));
                    proof {
                        safe_add_preserves_parity(val);
                        assert(safe_add(val) % 2 != val % 2);
                        assert(val % 2 == 1);
                        assert(safe_add(val) % 2 == 0);
                        assert(N % 2 == 0);
                    }
                }
            } else {
                if a[i] % 2 == 0 {
                    let val = a[i];
                    a.set(i, safe_add(val));
                    proof {
                        safe_add_preserves_parity(val);
                        assert(safe_add(val) % 2 != val % 2);
                        assert(val % 2 == 0);
                        assert(safe_add(val) % 2 == 1);
                        assert(N % 2 == 1);
                    }
                }
            }
        }
        i += 1;
    }
}
// </vc-code>

}

fn main() {}