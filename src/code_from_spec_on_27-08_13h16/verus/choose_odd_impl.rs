use vstd::prelude::*;

verus!{

// <vc-helpers>
// No updates needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    // pre-conditions-start
    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        odd_index < v.len(),
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires
        exists |q: int| 0 <= q < v.len() && v[q] % 2 == 1,
    ensures
        odd_index < v.len(),
        v[odd_index] % 2 == 1,
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall |k: usize| 0 <= k < i ==> v[k] % 2 == 0,
        decreases v.len() - i,
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i = i + 1;
    }
    proof {
        assert(false); // This line should never be reached due to the precondition
    }
    unreachable!();
}
// </vc-code>

}

fn main() {}