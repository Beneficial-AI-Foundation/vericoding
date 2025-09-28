// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Fixed type conversion from usize to int */
fn mod_op(x: i8, y: i8) -> (r: i8)
    requires y != 0,
    ensures r == x % y,
{
    let mut r_val = x;
    while r_val >= y
        invariant
            r_val >= 0,
            r_val == x % y,
        decreases r_val,
    {
        r_val = r_val - y;
    }
    r_val
}

// </vc-helpers>

// <vc-spec>
fn remainder(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion from usize to int */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] % b@[j],
        decreases a.len() - i,
    {
        assert(i < a.len());
        let i_int: int = i as int;
        assert(0 <= i_int < b@.len()) by {
            assert(0 <= i_int < b@.len());
        }
        assert(b@[i_int] != 0) by {
            assert(forall|k: int| 0 <= k < b@.len() ==> b@[k] != 0);
        }
        let rem = mod_op(a@[i_int], b@[i_int]);
        result.push(rem);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}