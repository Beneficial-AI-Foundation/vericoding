// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): return element at int index */
fn get_elem(ary: Vec<i8>, i: int) -> i8
    requires
        0 <= i, i < ary.len() as int,
{
    ary[i as usize]
}
// </vc-helpers>

// <vc-spec>
fn numpy_ediff1d(ary: Vec<i8>) -> (result: Vec<i8>)
    requires ary.len() > 0,
    ensures 
        result.len() == ary.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == ary[i + 1] as int - ary[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement ediff1d using int-based invariant for ary indexing */
    let n: usize = ary.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n - 1
        invariant
            0 <= i as int,
            result.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> result[j as usize] as int == ary[j + 1] as int - ary[j] as int,
        decreases (n - 1) as int - i as int
    {
        let d: i8 = ary[i + 1] - ary[i];
        result.push(d);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}