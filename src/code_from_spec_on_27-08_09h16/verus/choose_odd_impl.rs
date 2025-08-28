use vstd::prelude::*;

verus!{

// <vc-helpers>
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
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,
        decreases v.len() - i
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    0
}
// </vc-code>

}

fn main() {}