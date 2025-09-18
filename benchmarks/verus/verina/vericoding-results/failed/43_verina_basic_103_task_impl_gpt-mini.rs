// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute element replacement based on index using usize */
fn compute_replacement(a: &Vec<i32>, i: usize) -> i32
    requires
        i < a.len(),
{
    if i == 4 {
        a[i] + 3
    } else if i == 7 {
        516
    } else {
        a[i]
    }
}

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
    /* code modified by LLM (iteration 5): build result by iterating with usize indices and using helper */
    let n: usize = a.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            forall|k: usize| k < i ==> ((k == 4 ==> result[k] == a[k] + 3) && (k == 7 ==> result[k] == 516) && ((k != 4 && k != 7) ==> result[k] == a[k])),
        decreases n - i
    {
        let val = compute_replacement(a, i);
        result.push(val);
        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}