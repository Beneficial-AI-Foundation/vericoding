// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple conditional chooser */
fn choose(c: bool, a: i8, b: i8) -> i8 {
    if c { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn where_fn(condition: Vec<bool>, x: Vec<i8>, y: Vec<i8>) -> (result: Vec<i8>)
    requires 
        condition.len() == x.len(),
        x.len() == y.len(),
    ensures 
        result.len() == condition.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] as int == if condition[i] { x[i] as int } else { y[i] as int }
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn where_with_transform(arr: Vec<i8>) -> (result: Vec<i8>)
    requires arr.len() >= 0,
    ensures 
        result.len() == arr.len()
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement where_fn body with element-wise choice and invariant */
    let mut res = Vec::<i8>::new();
    let n = condition.len();
    let mut idx: nat = 0;
    while idx < n
        invariant
            idx <= n,
            res.len() == idx,
            forall|j: int| 0 <= j < idx ==> res[j] as int == if condition[j] { x[j] as int } else { y[j] as int },
        decreases n - idx
    {
        let c = condition[idx];
        let a = x[idx];
        let b = y[idx];
        res.push(choose(c, a, b));
        idx = idx + 1;
    }
    res
}

{
    /* code modified by LLM (iteration 5): implement where_with_transform body (identity transform) */
    let mut res = Vec::<i8>::new();
    let n = arr.len();
    let mut i: nat = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
        decreases n - i
    {
        let v = arr[i];
        res.push(v);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}