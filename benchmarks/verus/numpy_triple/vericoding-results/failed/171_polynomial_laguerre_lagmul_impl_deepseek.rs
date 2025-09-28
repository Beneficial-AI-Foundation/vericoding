// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

#[verifier::spec]
fn lagmul_spec_term(c1: Seq<f64>, c2: Seq<f64>, i: int) -> f64
    decreases i
{
    if i < 0 {
        0.0
    } else if i == 0 {
        c1.index(0) * c2.index(0)
    } else {
        lagmul_spec_term(c1, c2, i - 1) + c1.index(i) * c2.index(0) + if i - 1 >= 0 { c1.index(i - 1) * c2.index(1) } else { 0.0 }
    }
}

#[verifier::spec]
fn lagmul_spec(c1: Seq<f64>, c2: Seq<f64>) -> Seq<f64> {
    if c1.len() > 0 && c2.len() > 0 {
        let n: nat = (c1.len() + c2.len() - 1) as nat;
        Seq::new(n, |i: int| lagmul_spec_term(c1, c2, i))
    } else {
        Seq::empty()
    }
}

proof fn lagmul_spec_proof(c1: Seq<f64>, c2: Seq<f64>, i: int)
    requires 
        0 <= i < c1.len() + c2.len() - 1,
        c1.len() > 0,
        c2.len() > 0
    ensures 
        lagmul_spec(c1, c2)[i] != 0.0 ==> 
            exists|j: int, k: int| 
                0 <= j < c1.len() && 
                0 <= k < c2.len() && 
                j + k == i && 
                c1.index(j) != 0.0 && 
                c2.index(k) != 0.0
    decreases i
{
    if i >= 0 {
        reveal(lagmul_spec_term);
        if i > 0 {
            lagmul_spec_proof(c1, c2, i - 1);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn lagmul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires c1@.len() > 0 && c2@.len() > 0,
    ensures 
        result@.len() == c1@.len() + c2@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> 
            (result@[i] != 0.0 ==> 
                exists|j: int, k: int| 
                    0 <= j < c1@.len() && 
                    0 <= k < c2@.len() && 
                    j + k == i && 
                    c1@[j] != 0.0 && 
                    c2@[k] != 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed integer comparisons and sequence indexing */
    let n: usize = c1.len() + c2.len() - 1;
    let mut result = Vec::new();
    result.resize(n, 0.0);
    
    let ghost n_int: int = n as int;
    
    let mut i: usize = 0;
    while i < n
        invariant 
            i <= n,
            result@.len() == n,
            forall|idx: int| 0 <= idx < i as int ==> result@[idx] == lagmul_spec(c1@, c2@)[idx]
        decreases n - i
    {
        let ghost i_int: int = i as int;
        result.set(i, lagmul_spec_term(c1@, c2@, i_int) as f64);
        i += 1;
    }
    
    proof {
        lagmul_spec_proof(c1@, c2@, n_int - 1);
    }
    
    result
}
// </vc-code>

}
fn main() {}