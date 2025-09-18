// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): XOR of non-negative i32 is non-negative using bitvector semantics */
proof fn lemma_xor_nonneg(a: i32, b: i32)
    requires
        a >= 0i32,
        b >= 0i32,
    ensures
        (a ^ b) >= 0i32
{
    assert((a ^ b) >= 0i32);
}

/* helper modified by LLM (iteration 5): XOR with zero returns the other operand (identities) */
proof fn lemma_xor_zero(b: i32)
    ensures
        (0i32 ^ b) == b,
        (b ^ 0i32) == b
{
    assert((0i32 ^ b) == b);
    assert((b ^ 0i32) == b);
}

/* helper modified by LLM (iteration 5): XOR of a value with itself is zero */
proof fn lemma_xor_self_zero(a: i32)
    ensures
        (a ^ a) == 0i32
{
    assert((a ^ a) == 0i32);
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
    /* code modified by LLM (iteration 5): fix cast usage and spec-index bridging; use n instead of x1.len() inside proof to avoid parse issue */
    let n: usize = x1.len();
    let mut result_vec: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            result_vec.len() == i,
            n == x1.len(),
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i as int ==> result_vec@[j] == (x1[j] ^ x2[j]),
        decreases n as int - i as int
    {
        let a: i32 = x1[i];
        let b: i32 = x2[i];
        let c: i32 = a ^ b;
        result_vec.push(c);
        proof {
            assert(0 <= i as int && i as int < n as int);
            assert(a == x1[i]);
            assert(b == x2[i]);
            assert(c == (x1[i] ^ x2[i]));
            assert forall|j: int| 0 <= j < i as int + 1 ==> result_vec@[j] == (x1[j] ^ x2[j]) by {
                if j < i as int {
                    // preserved by invariant
                } else {
                    assert(j == i as int);
                    assert(result_vec@[j] == c);
                    assert(result_vec@[j] == (x1[j] ^ x2[j]));
                }
            }
        }
        i = i + 1;
    }

    proof {
        assert(i == n);
        assert(result_vec.len() == x1.len());
        assert(forall|j: int| 0 <= j < result_vec.len() as int ==> result_vec@[j] == (x1[j] ^ x2[j]));

        assert forall|j: int| 0 <= j < result_vec.len() as int ==> result_vec@[j] >= 0i32 by {
            let a = x1[j];
            let b = x2[j];
            assert(0 <= j && j < n as int);
            assert(a >= 0i32);
            assert(b >= 0i32);
            lemma_xor_nonneg(a, b);
            assert(result_vec@[j] == (a ^ b));
        }

        assert forall|j: int| 0 <= j < result_vec.len() as int && x1[j] == 0i32 ==> result_vec@[j] == x2[j] by {
            if x1[j] == 0i32 {
                lemma_xor_zero(x2[j]);
                assert(result_vec@[j] == (x1[j] ^ x2[j]));
                assert(result_vec@[j] == x2[j]);
            }
        }

        assert forall|j: int| 0 <= j < result_vec.len() as int && x2[j] == 0i32 ==> result_vec@[j] == x1[j] by {
            if x2[j] == 0i32 {
                lemma_xor_zero(x1[j]);
                assert(result_vec@[j] == (x1[j] ^ x2[j]));
                assert(result_vec@[j] == x1[j]);
            }
        }

        assert forall|j: int| 0 <= j < result_vec.len() as int && x1[j] == x2[j] ==> result_vec@[j] == 0i32 by {
            if x1[j] == x2[j] {
                lemma_xor_self_zero(x1[j]);
                assert(result_vec@[j] == (x1[j] ^ x2[j]));
                assert(result_vec@[j] == 0i32);
            }
        }
    }

    result_vec
}
// </vc-code>

}
fn main() {}