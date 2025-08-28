use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mul_bounds(a: i32, b: i32)
    ensures
        (a as i64) * (b as i64) <= (i32::MAX as i64) * (i32::MAX as i64),
        (a as i64) * (b as i64) >= (i32::MIN as i64) * (i32::MIN as i64),
{
    let a64 = a as i64;
    let b64 = b as i64;
    let max64 = i32::MAX as i64;
    let min64 = i32::MIN as i64;
    
    assert(a64 <= max64);
    assert(a64 >= min64);
    assert(b64 <= max64);
    assert(b64 >= min64);
    
    // Prove upper bound
    if a64 >= 0 && b64 >= 0 {
        assert(a64 * b64 <= max64 * b64);
        assert(max64 * b64 <= max64 * max64);
        assert(a64 * b64 <= max64 * max64);
    } else if a64 <= 0 && b64 <= 0 {
        assert(a64 * b64 >= min64 * b64);
        assert(min64 * b64 >= min64 * min64);
        assert(a64 * b64 >= min64 * min64);
        assert(min64 * min64 <= max64 * max64);
        assert(a64 * b64 <= max64 * max64);
    } else if a64 >= 0 && b64 <= 0 {
        assert(a64 * b64 <= max64 * b64);
        assert(max64 * b64 <= max64 * 0);
        assert(max64 * 0 == 0);
        assert(0 <= max64 * max64);
        assert(a64 * b64 <= max64 * max64);
    } else {
        assert(a64 * b64 <= a64 * min64);
        assert(a64 * min64 <= 0);
        assert(0 <= max64 * max64);
        assert(a64 * b64 <= max64 * max64);
    }
    
    // Prove lower bound
    if a64 >= 0 && b64 >= 0 {
        assert(a64 * b64 >= 0);
        assert(0 >= min64 * min64);
        assert(a64 * b64 >= min64 * min64);
    } else if a64 <= 0 && b64 <= 0 {
        assert(a64 * b64 >= min64 * b64);
        assert(min64 * b64 >= min64 * min64);
        assert(a64 * b64 >= min64 * min64);
    } else if a64 >= 0 && b64 <= 0 {
        assert(a64 * b64 >= a64 * min64);
        assert(a64 * min64 >= max64 * min64);
        assert(max64 * min64 >= min64 * min64);
        assert(a64 * b64 >= min64 * min64);
    } else {
        assert(a64 * b64 >= min64 * b64);
        assert(min64 * b64 >= min64 * min64);
        assert(a64 * b64 >= min64 * min64);
    }
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
    let len = a.len();
    let mut result: Vec<i64> = Vec::with_capacity(len);
    let mut i: usize = 0;
    
    while i < len
        invariant
            len == a.len(),
            len == b.len(),
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == (a[j] as i64) * (b[j] as i64),
        decreases len - i
    {
        let prod = (a[i] as i64) * (b[i] as i64);
        proof {
            lemma_mul_bounds(a[i], b[i]);
        }
        result.push(prod);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}