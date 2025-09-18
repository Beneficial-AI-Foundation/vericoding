// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn full<T>(n: usize, fill_value: T) -> (result: Vec<T>)
    ensures 
        result.len() == n,

        forall|i: int| 0 <= i < n ==> result[i] == fill_value,

        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> result[i] == result[j],

        n > 0 ==> result[0] == fill_value,
        n > 0 ==> result[(n-1) as int] == fill_value,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Implemented efficient loop-based creation with proper invariants for verification */{
    let mut result = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] == fill_value,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < i ==> result@[k] == result@[l],
        decreases n - i,
    {
        result.push(fill_value.clone());
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}