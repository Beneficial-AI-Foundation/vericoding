// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add Clone trait bound and fix properties */
proof fn lemma_vec_full_properties<T: Clone>(v: Vec<T>, n: nat, fill_value: T)
    ensures
        v.len() == n ==> (
            forall|i: int| 0 <= i < n ==> v[i] == fill_value
            && forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> v[i] == v[j]
            && (n > 0 ==> v[0] == fill_value)
            && (n > 0 ==> v[(n-1) as int] == fill_value)
        ),
{
    if v.len() == n {
        assert forall|i: int| 0 <= i < n implies v[i] == fill_value by {
            assert(v[i] == fill_value);
        };
        assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n implies v[i] == v[j] by {
            assert(v[i] == fill_value);
            assert(v[j] == fill_value);
        };
        if n > 0 {
            assert(v[0] == fill_value);
            assert(v[(n-1) as int] == fill_value);
        }
    }
}
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
/* code modified by LLM (iteration 5): fix clone method not found error */
{
    let mut result = Vec::new();
    
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == fill_value,
            decreases n - i,
    {
        result.push(fill_value);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}