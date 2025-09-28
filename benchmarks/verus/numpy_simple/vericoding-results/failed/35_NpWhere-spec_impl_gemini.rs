// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by providing a full function definition */
fn where_fn(condition: Vec<bool>, x: Vec<i8>, y: Vec<i8>) -> (result: Vec<i8>)
    requires 
        condition.len() == x.len(),
        x.len() == y.len(),
    ensures 
        result.len() == condition.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] as int == if condition[i] { x[i] as int } else { y[i] as int }
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < condition.len()
        invariant
            i <= condition.len(),
            result.len() == i,
            condition.len() == x.len(),
            x.len() == y.len(),
            forall|j: int| 0 <= j < i as int ==> 
                result[j] as int == if condition[j] { x[j] as int } else { y[j] as int },
        decreases condition.len() - i
    {
        if condition[i] {
            result.push(x[i]);
        } else {
            result.push(y[i]);
        }
        i = i + 1;
    }
    result
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
/* code modified by LLM (iteration 5): fixed compilation error by providing a full function definition */
fn where_with_transform(arr: Vec<i8>) -> (result: Vec<i8>)
    requires arr.len() >= 0,
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] as int == if arr[i] >= 0 { arr[i] as int } else { 0 }
{
    let mut condition = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            condition.len() == i,
            forall|j: int| 0 <= j < i as int ==> (condition[j] <==> (arr[j] >= 0)),
        decreases arr.len() - i
    {
        condition.push(arr[i] >= 0);
        i = i + 1;
    }

    let mut y = Vec::new();
    let mut k: usize = 0;
    while k < arr.len()
        invariant
            k <= arr.len(),
            y.len() == k,
            forall|l: int| 0 <= l < k as int ==> y[l] == 0i8,
        decreases arr.len() - k
    {
        y.push(0i8);
        k = k + 1;
    }

    let result = where_fn(condition, arr, y);
    result
}
// </vc-code>


}
fn main() {}