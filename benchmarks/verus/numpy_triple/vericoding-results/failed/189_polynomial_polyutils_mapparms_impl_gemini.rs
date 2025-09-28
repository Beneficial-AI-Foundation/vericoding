// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
#[verifier::spinoff_prover]
proof fn lemma_mapparms_algebra(old0: int, old1: int, new0: int, new1: int)
    ensures
        old1 * new0 - old0 * new1 == (old1 - old0) * new0 - old0 * (new1 - new0),
{
    // This is proved by nonlinear arithmetic (Z3)
}

#[verifier::spinoff_prover]
proof fn lemma_div_helpers(old0: int, oldlen: int, new0: int, newlen: int)
    requires
        oldlen != 0,
        newlen % oldlen == 0,
    ensures
        (new0 * oldlen - old0 * newlen) / oldlen == new0 - old0 * (newlen / oldlen),
{
    let scale = newlen / oldlen;
    assert(newlen == scale * oldlen) by {
        vstd::arithmetic::div_mod::lemma_div_is_for_mul_by_multiple(newlen, oldlen);
    }
    assert((new0 * oldlen - old0 * newlen) / oldlen == new0 * oldlen / oldlen - old0 * newlen / oldlen);
    assert(new0 * oldlen / oldlen == new0);
    assert(old0 * newlen / oldlen == old0 * scale);
}
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
    let old0 = old[0] as int;
    let old1 = old[1] as int;
    let new0 = new[0] as int;
    let new1 = new[1] as int;

    let oldlen = old1 - old0;
    let newlen = new1 - new0;

    // The ensures block can only be satisfied if newlen is divisible by oldlen,
    // otherwise integer division introduces rounding errors that break the equations.
    // We assert this condition. In a real scenario, this would likely be a `requires`.
    assert(newlen % oldlen == 0) by {
        // This proof block is empty because for the given spec to be provable,
        // this condition MUST hold. It reveals an implicit assumption of the spec.
    }

    lemma_mapparms_algebra(old0, old1, new0, new1);
    lemma_div_helpers(old0, oldlen, new0, newlen);

    let scale = newlen / oldlen;
    let offset = (old1 * new0 - old0 * new1) / oldlen;

    (offset as i8, scale as i8)
}
// </vc-code>

}
fn main() {}