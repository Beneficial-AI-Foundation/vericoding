use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mul_in_range(a: i32, b: i32)
    ensures
        (a as i64) * (b as i64) == spec_mul_64(a, b)
{
}

proof fn lemma_vec_indexing<T>(v: Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v@[i] == v[i],
{
}

spec fn spec_mul_64(a: i32, b: i32) -> i64 {
    (a as i64) * (b as i64) as i64
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_product(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i64>) by (nonlinear_arith)
    // pre-conditions-start
    requires
        a.len() == b.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| #![auto] 0 <= i && i < a.len() ==> result[i] == (a[i] as i64) * (b[i] as i64),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i64> = Vec::with_capacity(a.len());
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|j: int| 0 <= j && j < idx ==> result@[j] == spec_mul_64(a[j as usize], b[j as usize]),
    {
        let a_val = a[idx];
        let b_val = b[idx];
        proof {
            lemma_mul_in_range(a_val, b_val);
            lemma_vec_indexing(a, idx as int);
            lemma_vec_indexing(b, idx as int);
        }
        let product = spec_mul_64(a_val, b_val);
        result.push(product);
        idx = idx + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}