// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn flatnonzero(a: Vec<f64>) -> (result: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < result.len() ==> a[result[i] as int] != 0.0,

        forall|j: int| 0 <= j < a.len() && a[j] != 0.0 ==> exists|k: int| 0 <= k < result.len() && result[k] == j,

        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
// </vc-spec>
// <vc-code>
{"\n    /* code modified by LLM (iteration 3): implemented flatnonzero function with loop to collect non-zero indices */\n    let mut result: Vec<usize> = Vec::new();\n    let mut i: usize = 0;\n    while i < a.len()\n        invariant\n            0 <= i <= a.len(),\n            forall|k: int| 0 <= k < result.len() ==> a[result[k] as int] != 0.0,\n            forall|j: int| 0 <= j < i && a[j] != 0.0 ==> exists|k: int| 0 <= k < result.len() && result[k] == (j as usize),\n            forall|k1: int, k2: int| 0 <= k1 < result.len() && 0 <= k2 < result.len() && k1 != k2 ==> result[k1 as int] != result[k2 as int],\n            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1 as int] < result[k2 as int],\n        decreases a.len() - i\n    {\n        if a[i] != 0.0 {\n            result.push(i);\n        }\n        i += 1;\n    }\n    result\n}"
// </vc-code>

}
fn main() {}