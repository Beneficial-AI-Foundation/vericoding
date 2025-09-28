// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retain a simple no-op proof helper; no extra lemmas required */
proof fn trivial_helper() { }

// </vc-helpers>

// <vc-spec>
fn modify_array_element(arr: Vec<Vec<nat>>, index1: usize, index2: usize, val: nat) -> (result: Vec<Vec<nat>>)
    requires
        index1 < arr.len(),
        index2 < arr[index1 as int].len(),
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() && i != index1 ==> result[i] == arr[i],
        forall|j: int| 0 <= j < arr[index1 as int].len() && j != index2 ==> result[index1 as int][j] == arr[index1 as int][j],
        result[index1 as int][index2 as int] == val,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct the result vector element-by-element with loop invariants to preserve rows except the targeted element */
    let n = arr.len();
    let mut result: Vec<Vec<nat>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i && k != index1 ==> result[k] == arr[k],
            if index1 < i {
                result[index1 as int].len() == arr[index1 as int].len(),
                forall|j: int| 0 <= j < arr[index1 as int].len() && j != index2 ==> result[index1 as int][j] == arr[index1 as int][j],
                result[index1 as int][index2 as int] == val
            } else { true },
        decreases n - i
    {
        if i == index1 {
            let m = arr[i as int].len();
            let mut row: Vec<nat> = Vec::new();
            let mut j: usize = 0;
            while j < m
                invariant
                    j <= m,
                    row.len() == j,
                    forall|t: int| 0 <= t < j && t != index2 ==> row[t] == arr[i as int][t],
                    if index2 < j { row[index2 as int] == val } else { true },
                decreases m - j
            {
                if j == index2 {
                    row.push(val);
                } else {
                    row.push(arr[i as int][j as int]);
                }
                j += 1;
            }
            assert(row.len() == arr[i as int].len());
            proof {
                assert(forall|t: int| 0 <= t < arr[i as int].len() && t != index2 ==> row[t] == arr[i as int][t]);
                assert(index2 < arr[i as int].len());
                assert(row[index2 as int] == val);
            }
            result.push(row);
        } else {
            let row = arr[i as int].clone();
            result.push(row);
            assert(result[i as int] == arr[i as int]);
        }
        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}