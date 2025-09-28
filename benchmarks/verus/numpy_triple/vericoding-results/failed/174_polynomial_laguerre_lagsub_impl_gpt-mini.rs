// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): round-trip cast between i8 and int */
fn i8_int_roundtrip(a: i8)
    ensures
        (a as int) as i8 == a,
{
    proof {
        assert((a as int) as i8 == a);
    }
}

/* helper modified by LLM (iteration 5): relate i64 runtime subtraction to spec int subtraction for i8 operands */
fn i8_i64_sub_eq(a: i8, b: i8)
    ensures
        ((a as i64) - (b as i64)) as int == a as int - b as int,
{
    proof {
        // cast a and b through i64 to int match direct cast to int
        assert((a as i64) as int == a as int);
        assert((b as i64) as int == b as int);
        // difference preserved through casts
        assert(((a as i64) - (b as i64)) as int == (a as i64) as int - (b as i64) as int);
        assert((a as i64) as int - (b as i64) as int == a as int - b as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn lagsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires c1.len() == c2.len(),
    ensures 
        result.len() == c1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == c1[i] as int - c2[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use int index for Vec indexing; compute elementwise subtraction using i64 and cast back to i8 */
    let n = c1.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            result.len() == i,
            forall|k: int| 0 <= k && k < (i as int) ==> result[k] as int == c1[k] as int - c2[k] as int,
        decreases n - i
    {
        let idx: int = i as int;
        let d: i64 = (c1[idx] as i64) - (c2[idx] as i64);
        result.push(d as i8);
        proof {
            // relate runtime subtraction to the specification-level subtraction
            i8_i64_sub_eq(c1[idx], c2[idx]);
            assert((d as int) == c1[idx] as int - c2[idx] as int);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}