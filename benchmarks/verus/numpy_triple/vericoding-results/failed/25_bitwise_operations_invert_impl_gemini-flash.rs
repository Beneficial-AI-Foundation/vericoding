// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed in helpers. */
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
/* code modified by LLM (iteration 5): Fixed compilation error by changing `x_seq.index(i as int)` to `x_seq[i]` because index operator on `Seq<T>` takes `nat` or `int` for ghost code, but `i` is `usize`. The previous attempt to cast `i` to `int` was causing issues. Using direct access `x_seq[i]` is appropriate as `i` is already in a valid range. */
{
    let mut result = Vec::new();
    let x_len = x.len();
    let x_seq = x.to_seq();
    let mut i: usize = 0;

    while i < x_len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == -(x_seq[j] + 1),
            forall|j: int| 0 <= j < i ==> (x_seq[j] == 0 <==> result[j] == -1),
            forall|j: int| 0 <= j < i ==> (x_seq[j] == -1 <==> result[j] == 0),
            forall|j: int| 0 <= j < i && x_seq[j] != -1 ==> (x_seq[j] > 0 <==> result[j] < 0),
            0 <= i <= x_len,
        decreases x_len - i
    {
        let val_x = x_seq[i];
        let val_result = -(val_x + 1);
        result.push(val_result);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}