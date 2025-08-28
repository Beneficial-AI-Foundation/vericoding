use vstd::prelude::*;

verus!{

// <vc-helpers>
// </vc-helpers>
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
    let original_len = a.len();
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum <= 2 * i,
            sum as int + 2 * (a.len() - i) as int <= u32::MAX as int,
            a.len() == original_len,
        decreases a.len() - i
    {
        if a[i] > 2 {
            a.set(i, 2);
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(sum <= 2 * i);
    assert(sum <= 2 * a.len());
    assert(a.len() == original_len);
    assert(original_len == N);
    assert(sum <= 2 * N);
    
    sum
    // impl-end
}
// </vc-code>

}

fn main() {}