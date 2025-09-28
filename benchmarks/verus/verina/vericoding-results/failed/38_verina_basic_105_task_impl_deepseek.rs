// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma_abs_product assertions with proper case analysis */
proof fn lemma_abs_product(x: int, y: int)
    ensures abs(x * y) == abs(x) * abs(y),
{
    if x >= 0 {
        if y >= 0 {
            assert(x * y >= 0);
            assert(abs(x * y) == x * y);
            assert(abs(x) == x);
            assert(abs(y) == y);
            assert(abs(x) * abs(y) == x * y);
        } else {
            assert(x * y <= 0);
            assert(abs(x * y) == -(x * y));
            assert(abs(x) == x);
            assert(abs(y) == -y);
            assert(abs(x) * abs(y) == x * (-y));
            assert(-(x * y) == x * (-y));
        }
    } else {
        if y >= 0 {
            assert(x * y <= 0);
            assert(abs(x * y) == -(x * y));
            assert(abs(x) == -x);
            assert(abs(y) == y);
            assert(abs(x) * abs(y) == (-x) * y);
            assert(-(x * y) == (-x) * y);
        } else {
            assert(x * y >= 0);
            assert(abs(x * y) == x * y);
            assert(abs(x) == -x);
            assert(abs(y) == -y);
            assert(abs(x) * abs(y) == (-x) * (-y));
            assert((-x) * (-y) == x * y);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn array_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed array bounds access with proper verification */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i as nat,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] as int * b[j] as int,
        decreases a.len() - i,
    {
        assert(i < a.len()) by {
            assert(i < a.len());
        };
        let ai = a[i];
        let bi = b[i];
        let product = ai * bi;
        result.push(product);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}