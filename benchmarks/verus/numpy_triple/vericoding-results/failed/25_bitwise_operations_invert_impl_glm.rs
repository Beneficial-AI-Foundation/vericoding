// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn invert(x: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == -(x[i] + 1),
        forall|i: int| 0 <= i < x.len() && x[i] == 0 ==> result[i] == -1,
        forall|i: int| 0 <= i < x.len() && x[i] == -1 ==> result[i] == 0,
        forall|i: int| 0 <= i < x.len() && x[i] != -1 ==> (x[i] > 0 <==> result[i] < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type of loop index to int and used sequence view for length */
    let mut result: Vec<i32> = Vec::new();
    let n = x@.len();   // n is nat
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == -(x@[j] + 1),
            forall|j: int| 0 <= j < i && x@[j] != -1 ==> (x@[j] > 0 <==> result@[j] < 0),
        decreases n - i
    {
        assert(i < x@.len());   // we can use x@.len() or n, both are the same
        let val = x[i as usize];   // Rust vector indexing requires usize
        let new_val = !val;
        result.push(new_val);
        assert(result@[i] == new_val);
        assert(new_val == -(val + 1));
        if val != -1 {
            assert(val > 0 <==> new_val < 0);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}