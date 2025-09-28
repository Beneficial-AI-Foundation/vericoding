// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [fixed compilation error by using correct vstd lemma `lemma_div_is_strictly_smaller`] */
proof fn lemma_half_lt_self(n: int)
    requires n > 0,
    ensures n / 2 < n,
{
    if n > 1 {
        vstd::arithmetic::div_mod::lemma_div_is_strictly_smaller(n, 2);
    } else { // n == 1
        assert(n / 2 == 0);
    }
}

/* helper modified by LLM (iteration 5): [fixed compilation errors by using correct vstd lemmas `lemma_mul_left_inequality` and `lemma_div_is_zero`] */
proof fn lemma_freq_is_zero(i: int, n: int, d: int)
    requires
        n > 0,
        d > 0,
        0 <= i <= n / 2,
    ensures
        i / (d * n) == 0,
{
    lemma_half_lt_self(n);
    vstd::arithmetic::mul::lemma_mul_left_inequality(1, d, n);
    vstd::arithmetic::div_mod::lemma_div_is_zero(i, d * n);
}
// </vc-helpers>

// <vc-spec>
fn numpy_rfftfreq(n: usize, d: i8) -> (result: Vec<i8>)
    requires 
        n > 0,
        d > 0,
    ensures
        result.len() == n / 2 + 1,
        result@[0] == 0,
        forall|i: int| 0 <= i < result.len() ==> result@[i] == i / ((d as int) * (n as int)),
        result@[(n / 2) as int] == (n / 2) as int / ((d as int) * (n as int)),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result@[i] <= result@[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [fixed dependencies by correcting helper function implementations] */
{
    let len = n / 2 + 1;
    let mut result: Vec<i8> = Vec::with_capacity(len);
    let mut i: usize = 0;
    while i < len
        invariant
            n > 0,
            d > 0,
            len == n / 2 + 1,
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == j / ((d as int) * (n as int)),
            forall|j: int, k: int| 0 <= j <= k < i ==> result@[j] <= result@[k],
        decreases len - i
    {
        proof {
            lemma_freq_is_zero(i as int, n as int, d as int);
        }

        result.push(0i8);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}