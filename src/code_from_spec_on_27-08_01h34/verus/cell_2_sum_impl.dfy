use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn sum_bound_holds(a: &Vec<u32>, n: usize) -> bool {
    forall|i: int| 0 <= i < n ==> a@[i] <= 2
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    // pre-conditions-start
    requires 
        old(a).len() == N,
        N <= 0x7FFF_FFFF,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum <= 2*N,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut sum: u32 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            sum <= 2 * (i as u32),
            forall|j: int| 0 <= j < i ==> a@[j] <= 2,
        decreases a.len() - i
    {
        if a[i] > 2 {
            a.set(i, 2);
        }
        proof {
            assert(a@[i as int] <= 2);
            assert(sum <= 2 * (i as u32));
            assert(2 * (i as u32) + a@[i as int] <= 2 * (i as u32) + 2);
            assert(2 * (i + 1) == 2 * i + 2);
            assert(2 * (i as u32) + 2 <= 2 * ((i + 1) as u32)) by {
                assert(i < a.len());
                assert(i + 1 <= a.len());
                assert((i + 1) as u32 == (i as u32) + 1);
                assert(2 * ((i + 1) as u32) == 2 * ((i as u32) + 1));
                assert(2 * ((i as u32) + 1) == 2 * (i as u32) + 2);
            }
        }
        sum = sum + a[i];
        i = i + 1;
    }
    proof {
        assert(i == a.len());
        assert(sum <= 2 * (i as u32));
        assert(2 * (i as u32) == 2 * (a.len() as u32));
        assert(a.len() == N as usize);
        assert((a.len() as u32) == N);
    }
    sum
    // impl-end
}
// </vc-code>

}

fn main() {}