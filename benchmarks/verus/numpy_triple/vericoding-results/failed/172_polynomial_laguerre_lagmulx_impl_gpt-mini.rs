// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that index 0 is valid for non-empty vector */
fn lemma_len_positive_has_index0<T>(v: &Vec<T>)
    requires
        v@.len() > 0,
    ensures
        v@[0] == v@[0],
{
}

// </vc-helpers>

// <vc-spec>
fn lagmulx(c: Vec<i8>) -> (result: Vec<i8>)
    requires c@.len() > 0,
    ensures 
        result@.len() == c@.len() + 1,
        result@[0] as int == c@[0] as int,
        result@.len() >= 2 ==> result@[1] as int == -(c@[0] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct result vector of length n+1 with result[0]=c[0] and result[1]=-(c[0]) when applicable */
    let n = c.len();
    // Use helper to expose that c[0] is accessible when c is non-empty
    lemma_len_positive_has_index0(&c);
    let mut result: Vec<i8> = Vec::new();
    // push first element equal to c[0]
    result.push(c[0]);
    let mut j: usize = 1;
    while j <= n
        invariant
            result@.len() == j,
            j <= n,
        decreases n + 1 - j
    {
        if j == 1 {
            let neg_int: int = -(c[0] as int);
            result.push(neg_int as i8);
        } else {
            result.push(c[j - 1]);
        }
        j = j + 1;
    }
    result
}

// </vc-code>


}
fn main() {}