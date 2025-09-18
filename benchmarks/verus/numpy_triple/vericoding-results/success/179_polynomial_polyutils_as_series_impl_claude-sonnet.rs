// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_valid_array(arr: &Vec<Vec<f64>>) -> bool {
    arr.len() > 0 && forall|i: int| 0 <= i < arr.len() ==> arr[i].len() > 0
}

fn copy_vec(v: &Vec<f64>) -> (result: Vec<f64>)
    ensures result.len() == v.len(),
            forall|i: int| 0 <= i < v.len() ==> result[i] == v[i]
{
    let mut result = Vec::new();
    let mut idx = 0;
    while idx < v.len()
        invariant
            0 <= idx <= v.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == v[i]
        decreases v.len() - idx
    {
        result.push(v[idx]);
        idx += 1;
    }
    result
}

fn trim_vec(v: &Vec<f64>) -> (result: Vec<f64>)
    ensures forall|i: int| 0 <= i < result.len() ==> {
        result[i] == v[i] || result[i] == 0.0
    }
{
    let mut result = Vec::new();
    let mut idx = 0;
    while idx < v.len()
        invariant
            0 <= idx <= v.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> {
                result[i] == v[i] || result[i] == 0.0
            }
        decreases v.len() - idx
    {
        if v[idx] != 0.0 {
            result.push(v[idx]);
        } else {
            result.push(0.0);
        }
        idx += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn as_series(arr: Vec<Vec<f64>>, trim: bool) -> (result: Vec<Vec<f64>>)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> arr[i].len() > 0,
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            if !trim {
                result[i].len() == arr[i].len() &&
                forall|j: int| 0 <= j < arr[i].len() ==> result[i][j] == arr[i][j]
            } else {
                forall|j: int| 0 <= j < result[i].len() ==> {
                    result[i][j] == arr[i][j] || result[i][j] == 0.0
                }
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to main loop */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> {
                if !trim {
                    result[k].len() == arr[k].len() &&
                    forall|j: int| 0 <= j < arr[k].len() ==> result[k][j] == arr[k][j]
                } else {
                    forall|j: int| 0 <= j < result[k].len() ==> {
                        result[k][j] == arr[k][j] || result[k][j] == 0.0
                    }
                }
            }
        decreases arr.len() - i
    {
        let processed_row = if trim {
            trim_vec(&arr[i])
        } else {
            copy_vec(&arr[i])
        };
        result.push(processed_row);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}