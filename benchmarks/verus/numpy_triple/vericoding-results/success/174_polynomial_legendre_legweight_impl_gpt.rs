// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): exec/spec index equality for f32 vectors under bounds */
proof fn vec_index_eq_view_index_f32(v: Vec<f32>, i: int)
    requires
        0 <= i < v.len()
    ensures
        v[i] == v@[i]
{
    assert(v[i] == v@[i]);
}
// </vc-helpers>

// <vc-spec>
fn legweight(x: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1.0f32
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): use implies in forall proof and avoid helper call; build vector of ones */
    let n: usize = x.len();
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v.len() == i as int,
            forall|j: int| 0 <= j < v.len() ==> v@[j] == 1.0f32
        decreases (n - i) as int
    {
        v.push(1.0f32);
        i = i + 1;
    }
    assert forall|j: int| 0 <= j && j < v.len() implies v[j] == 1.0f32 by {
        assert(0 <= j && j < v.len());
        assert(v@[j] == 1.0f32);
        assert(v[j] == v@[j]);
    };
    v
}
// </vc-code>

}
fn main() {}