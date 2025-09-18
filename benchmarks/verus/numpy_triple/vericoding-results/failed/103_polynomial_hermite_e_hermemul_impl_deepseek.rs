// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed f64 operations by using direct arithmetic instead of method calls */
spec fn mul_seq(c1: Seq<f64>, c2: Seq<f64>) -> Seq<f64>
    recommends 
        c1.len() > 0,
        c2.len() > 0
{
    Seq::new((c1.len() + c2.len() - 1) as nat, |k: int| {
        if 0 <= k < c1.len() + c2.len() - 1 {
            let mut sum: f64 = 0.0;
            let mut i: int = 0;
            while i <= k {
                if i < c1.len() && k - i < c2.len() {
                    sum = sum + c1[i] * c2[k - i];
                }
                i = i + 1;
            }
            sum
        } else {
            0.0
        }
    })
}

proof fn lemma_mult_zero_property(c1: Seq<f64>, c2: Seq<f64>) 
    requires 
        c1.len() > 0,
        c2.len() > 0,
        (forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0.0) || (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0.0)
    ensures
        forall|k: int| 0 <= k < c1.len() + c2.len() - 1 ==> (#[trigger] mul_seq(c1, c2))[k] == 0.0
{
    if forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0.0 {
        assert forall|k: int| 0 <= k < c1.len() + c2.len() - 1 implies mul_seq(c1, c2)[k] == 0.0 by {
            let s = mul_seq(c1, c2);
            assert(s[k] == 0.0) by {
                assert forall|i: int| 0 <= i <= k implies (i < c1.len() && k - i < c2.len()) ==> c1[i] * c2[k - i] == 0.0 by {
                    assert(c1[i] == 0.0);
                };
            };
        };
    } else {
        assert(forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0.0);
        assert forall|k: int| 0 <= k < c1.len() + c2.len() - 1 implies mul_seq(c1, c2)[k] == 0.0 by {
            let s = mul_seq(c1, c2);
            assert(s[k] == 0.0) by {
                assert forall|i: int| 0 <= i <= k implies (i < c1.len() && k - i < c2.len()) ==> c1[i] * c2[k - i] == 0.0 by {
                    assert(c2[k - i] == 0.0);
                };
            };
        };
    }
}
// </vc-helpers>

// <vc-spec>
fn hermemul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        c1.len() > 0,
        c2.len() > 0,
    ensures
        result.len() == c1.len() + c2.len() - 1,
        (forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0.0) || 
        (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0.0) 
        ==> (forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed arithmetic operations by removing redundant f64 casts and using direct f64 operations */
{
    let mut result = Vec::new();
    let n = (c1.len() + c2.len() - 1) as usize;
    result.resize(n, 0.0);
    
    proof {
        lemma_mult_zero_property(c1@, c2@);
    }
    
    let mut k: usize = 0;
    while k < n {
        let mut sum: f64 = 0.0;
        let mut i: usize = 0;
        while i <= k {
            if i < c1.len() && k - i < c2.len() {
                sum = sum + c1[i] * c2[k - i];
            }
            i = i + 1;
        }
        result[k] = sum;
        k = k + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}