// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn is_non_zero_vector(v: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v[i] != 0
}

fn floor_divide(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == b.len(),
        is_non_zero_vector(a@.map(|i, x: i8| x as i32)),
        is_non_zero_vector(b@.map(|i, x: i8| x as i32)),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as i32 == (a[i] as i32) / (b[i] as i32),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed lambda syntax with parentheses around parameter list */
    let mut result = Vec::new();
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a.len(),
            n == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as i32 == (a[j] as i32) / (b[j] as i32),
            is_non_zero_vector(a@.map(|(k: int, x: i8)| x as i32)),
            is_non_zero_vector(b@.map(|(k: int, x: i8)| x as i32)),
    {
        let a_val = a[i];
        let b_val = b[i];
        assert(b_val != 0) by {
            assert(b@.map(|(k: int, x: i8)| x as i32)[i as int] == b[i] as i32);
            assert(is_non_zero_vector(b@.map(|(k: int, x: i8)| x as i32)));
            assert(0 <= i as int && i as int < b@.map(|(k: int, x: i8)| x as i32).len());
            assert(b@.map(|(k: int, x: i8)| x as i32)[i as int] != 0);
        };
        let quotient = (a_val as i32) / (b_val as i32);
        result.push(quotient as i8);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}