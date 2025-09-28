// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn create_filled_vector<T>(n: usize, fill_value: T) -> (v: Vec<T>)
    ensures
        v.len() == n,
        forall|i: int| 0 <= i < n ==> v[i] == fill_value,
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == fill_value,
        decreases n - i
    {
        v.push(fill_value);
        i += 1;
    }
    v
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
{
    create_filled_vector(n, fill_value)
}
// </vc-code>

}
fn main() {}