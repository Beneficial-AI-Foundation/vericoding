use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn has_odd_at_or_after(v: &Vec<u64>, start: int) -> bool {
    exists |q: int| start <= q < v.len() && v[q] % 2 == 1
}
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
            i <= v.len(),
            has_odd_at_or_after(v, i as int),
        decreases v.len() - i
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    unreached()
}
// </vc-code>

}

fn main() {}