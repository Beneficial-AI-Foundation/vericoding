// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn pow_int(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_int(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma relating Vec runtime length to its view length for proofs */
proof fn vec_len_view_eq<T>(v: &Vec<T>)
    ensures
        v.len() as int == v@.len(),
{
    assert(v.len() as int == v.view().len());
    assert(v.view().len() == v@.len());
}

// </vc-helpers>

// <vc-spec>
fn vander(x: Vec<i8>, m: usize) -> (result: Vec<Vec<i8>>)
    requires 
        x@.len() > 0,
        m > 0,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == m,
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < m ==> 
            result@[i]@[j] as int == pow_int(x@[i] as int, (m - 1 - j) as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build Vandermonde matrix with correct invariants and power computation using int arithmetic */
    let n: usize = x.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result@.len() == (i as int),
            i <= n,
        decreases n - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                row@.len() == (j as int),
                j <= m,
            decreases m - j
        {
            let base_rt: int = x[i] as int;
            let e0: nat = (m - 1 - j) as nat;
            let mut rem: usize = m - 1 - j;
            let mut p: int = 1;
            while rem > 0
                invariant
                    rem <= m,
                    p == pow_int(base_rt, (e0 - (rem as nat))),
                decreases rem
            {
                p = p * base_rt;
                rem -= 1;
            }
            proof {
                assert(p == pow_int(base_rt, e0));
            }
            let val: i8 = #[verifier::truncate] (p as i8);
            row.push(val);
            j += 1;
        }
        result.push(row);
        i += 1;
    }

    proof {
        vec_len_view_eq(&x);
        assert(result@.len() == (n as int));
        assert((n as int) == x@.len());
        assert(result@.len() == x@.len());
    }

    result
}

// </vc-code>


}
fn main() {}