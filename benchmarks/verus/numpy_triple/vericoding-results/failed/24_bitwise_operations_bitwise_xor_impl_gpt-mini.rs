// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): xor_zero_right lemma */
proof fn xor_zero_right(b: i32)
    ensures
        (0 ^ b) == b,
{
    assert((0 ^ b) == b);
}

/* helper modified by LLM (iteration 5): xor_zero_left lemma */
proof fn xor_zero_left(a: i32)
    ensures
        (a ^ 0) == a,
{
    assert((a ^ 0) == a);
}

/* helper modified by LLM (iteration 5): xor_self lemma */
proof fn xor_self(a: i32)
    ensures
        (a ^ a) == 0,
{
    assert((a ^ a) == 0);
}

/* helper modified by LLM (iteration 5): xor_nonneg lemma about non-negativity */
proof fn xor_nonneg(a: i32, b: i32)
    requires
        a >= 0,
        b >= 0,
    ensures
        (a ^ b) >= 0,
{
    let sign_mask: i32 = 1i32 << 31;
    // top bit of non-negative i32 values is zero
    assert((a & sign_mask) == 0);
    assert((b & sign_mask) == 0);
    // bitwise distribution: (x ^ y) & m == (x & m) ^ (y & m)
    assert(((a ^ b) & sign_mask) == ((a & sign_mask) ^ (b & sign_mask)));
    assert(((a & sign_mask) ^ (b & sign_mask)) == 0);
    assert(((a ^ b) & sign_mask) == 0);
    // if sign bit is zero, value is non-negative
    assert((a ^ b) >= 0);
}
// </vc-helpers>

// <vc-spec>
fn bitwise_xor(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] ^ x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == x2[i],
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute elementwise xor and prove non-negativity */
    let n: usize = x1.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> res[j] == (x1[j] ^ x2[j]),
            forall|j: int| 0 <= j < i as int ==> res[j] >= 0,
        decreases (n as int) - (i as int)
    {
        let old_i = i;
        let a: i32 = x1[old_i];
        let b: i32 = x2[old_i];
        res.push(a ^ b);
        proof {
            let old_i_int: int = old_i as int;
            assert(0 <= old_i_int && old_i_int < n as int);
            assert(x1[old_i_int] >= 0);
            assert(x2[old_i_int] >= 0);
            xor_nonneg(x1[old_i_int], x2[old_i_int]);
        }
        i = i + 1;
        proof {
            let old_i_int: int = old_i as int;
            assert(res[old_i_int] == a ^ b);
            assert(a == x1[old_i_int]);
            assert(b == x2[old_i_int]);
        }
    }
    res
}
// </vc-code>

}
fn main() {}