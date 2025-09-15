// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add3 helper */
spec fn add3(x: i32) -> i32 { x + 3 }
// </vc-helpers>

// <vc-spec>
fn update_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() >= 8,
    ensures
        result[4] == a[4] + 3,
        result[7] == 516,
        forall|i: int| 0 <= i < a.len() && i != 4 && i != 7 ==> result[i] == a[i],
        result.len() == a.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result vector with modified elements at indices 4 and 7 and prove postconditions */
    let mut r: Vec<i32> = Vec::new();
    let n: nat = a.len();
    let mut i: nat = 0;
    while i < n
        invariant i <= n;
        invariant r.len() == i;
        decreases n - i;
    {
        let idx: int = i as int;
        let val: i32 = if idx == 4 { a@[idx] + 3 } else if idx == 7 { 516 } else { a@[idx] };
        r.push(val);
        i = i + 1;
    }
    proof {
        let n_int: int = a.len() as int;
        let mut j: int = 0;
        while j < n_int
            invariant 0 <= j && j <= n_int;
            decreases n_int - j;
        {
            if j == 4 {
                assert(r@[j] == a@[j] + 3);
            } else if j == 7 {
                assert(r@[j] == 516);
            } else {
                assert(r@[j] == a@[j]);
            }
            j = j + 1;
        }
        assert(r.len() == a.len());
    }
    r
}
// </vc-code>

}
fn main() {}