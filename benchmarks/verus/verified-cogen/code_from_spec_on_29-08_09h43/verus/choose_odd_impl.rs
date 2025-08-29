use vstd::prelude::*;

verus!{

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    // impl-start
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            exists |q:int| i <= q < v.len() && v[q] % 2 == 1,
        /* code modified by LLM (iteration 3): added decreases clause to prove loop termination */
        decreases v.len() - i
    {
        if v[i] % 2 == 1 {
            return i;
        }
        /* code modified by LLM (iteration 2): strengthened loop invariant to maintain existence of odd element in remaining portion */
        i += 1;
    }
    0
    // impl-end
}
// </vc-code>

}

fn main() {}