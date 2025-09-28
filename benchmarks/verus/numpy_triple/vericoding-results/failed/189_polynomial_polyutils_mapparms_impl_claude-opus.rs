// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mapparms(old: [i8; 2], new: [i8; 2]) -> (result: (i8, i8))
    requires old[0] != old[1],
    ensures ({
        let (offset, scale) = result;
        let oldlen = old[1] as int - old[0] as int;
        let newlen = new[1] as int - new[0] as int;
        offset as int + scale as int * old[0] as int == new[0] as int &&
        offset as int + scale as int * old[1] as int == new[1] as int &&
        scale as int == newlen / oldlen &&
        offset as int == (old[1] as int * new[0] as int - old[0] as int * new[1] as int) / oldlen
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add overflow checks using checked arithmetic */
    // Calculate lengths with overflow checking
    let oldlen: i8 = old[1].checked_sub(old[0]).expect("oldlen overflow");
    let newlen: i8 = new[1].checked_sub(new[0]).expect("newlen overflow");
    
    // Calculate scale
    let scale: i8 = newlen / oldlen;
    
    // Calculate offset with overflow checking
    // offset = (old[1] * new[0] - old[0] * new[1]) / oldlen
    let term1: i8 = old[1].checked_mul(new[0]).expect("term1 overflow");
    let term2: i8 = old[0].checked_mul(new[1]).expect("term2 overflow");
    let numerator: i8 = term1.checked_sub(term2).expect("numerator overflow");
    let offset: i8 = numerator / oldlen;
    
    // Ghost assertions to help prove postconditions
    proof {
        assert(oldlen as int == old[1] as int - old[0] as int);
        assert(newlen as int == new[1] as int - new[0] as int);
        assert(scale as int == (newlen as int) / (oldlen as int));
        assert(offset as int == (old[1] as int * new[0] as int - old[0] as int * new[1] as int) / (oldlen as int));
        
        // Verify the linear mapping equations
        assert(offset as int + scale as int * old[0] as int == new[0] as int);
        assert(offset as int + scale as int * old[1] as int == new[1] as int);
    }
    
    (offset, scale)
}
// </vc-code>

}
fn main() {}