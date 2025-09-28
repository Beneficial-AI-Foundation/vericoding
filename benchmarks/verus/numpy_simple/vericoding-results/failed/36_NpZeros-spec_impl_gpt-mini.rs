// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide make_empty_vec */
fn make_empty_vec<T>() -> (v: Vec<T>)
    ensures
        v@.len() == 0,
{
    let v: Vec<T> = Vec::new();
    v
}

// </vc-helpers>

// <vc-spec>
fn zeros(n: usize) -> (result: Vec<i8>)
    ensures 
        result@.len() == n,
        forall|i: int| 0 <= i < n ==> result@[i] == 0
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn zeros2d(rows: usize, cols: usize) -> (result: Vec<Vec<i8>>)
    ensures 
        result@.len() == rows,
        forall|i: int| 0 <= i < rows ==> result@[i]@.len() == cols,
        forall|i: int, j: int| 0 <= i < rows && 0 <= j < cols ==> result@[i]@[j] == 0
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): implement zeros 1D */
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v@.len() == i,
            forall|k: int| 0 <= k < i ==> v@[k] == 0,
        decreases n - i
    {
        v.push(0);
        i += 1;
    }
    v
}

{
/* code modified by LLM (iteration 5): implement zeros2d 2D */
    let mut ret: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            ret@.len() == i,
            forall|r: int| 0 <= r < i ==> ret@[r]@.len() == cols,
            forall|r: int, c: int| 0 <= r < i && 0 <= c < cols ==> ret@[r]@[c] == 0,
        decreases rows - i
    {
        let mut v: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                v@.len() == j,
                forall|k: int| 0 <= k < j ==> v@[k] == 0,
            decreases cols - j
        {
            v.push(0);
            j += 1;
        }
        ret.push(v);
        i += 1;
    }
    ret
}

// </vc-code>


}
fn main() {}