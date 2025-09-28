// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): min helper for integers */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn all(a: Vec<f32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a@.len() ==> a@[i] != 0.0f32),
        (a@.len() == 0 ==> result == true),
        ((exists|i: int| 0 <= i < a@.len() && a@[i] == 0.0f32) ==> result == false),
        ((forall|i: int| 0 <= i < a@.len() ==> a@[i] != 0.0f32) ==> result == true),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate with int indices and convert length to int */
    let n: int = a@.len() as int;
    let mut i: int = 0 as int;
    let mut res: bool = true;
    while i < n
        invariant
            0 <= i && i <= n,
            res == (forall|j: int| 0 <= j && j < i ==> a@[j] != 0.0f32),
        decreases n - i
    {
        if a@[i] == 0.0f32 {
            res = false;
        }
        i = i + 1 as int;
    }
    res
}
// </vc-code>

}
fn main() {}