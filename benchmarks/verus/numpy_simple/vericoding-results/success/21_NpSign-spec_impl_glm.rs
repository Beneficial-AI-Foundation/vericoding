// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sign(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            (a[i] > 0 ==> result[i] == 1) &&
            (a[i] == 0 ==> result[i] == 0) &&
            (a[i] < 0 ==> result[i] == -1)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed sequence indexing syntax */
    let mut res = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len() as int,
            res.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (a@[j] > 0 ==> res@[j] == 1) &&
                (a@[j] == 0 ==> res@[j] == 0) &&
                (a@[j] < 0 ==> res@[j] == -1)
            }
        decreases (a.len() as int - i)
    {
        let x = a[i];
        let s = if x > 0 {
            1
        } else if x == 0 {
            0
        } else {
            -1
        };
        res.push(s);
        i += 1;
    }
    res
}
// </vc-code>


}
fn main() {}