// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn dsplit(arr: Vec<f32>, sections: usize) -> (result: Vec<Vec<f32>>)
    requires 
        sections > 0,
        arr.len() % sections == 0,
    ensures
        result.len() == sections,
        forall|i: int| 0 <= i < sections ==> result[i].len() == arr.len() / sections,
        forall|i: int, j: int| 0 <= i < sections && 0 <= j < (arr.len() / sections) ==> 
            result[i][j] == arr[i * (arr.len() / sections) + j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by adding parentheses around forall expressions in invariants to match Verus syntax */
    let len_per_section = arr.len() / sections;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut idx = 0;
    while idx < sections
        invariant result.len() == idx
        invariant (forall |k: int| 0 <= k < idx ==> result[k].len() == len_per_section)
        invariant (forall |k: int, j: int| 0 <= k < idx && 0 <= j < len_per_section ==> 
            result[k][j] == arr[k * len_per_section + j])
        decreases sections - idx
    {
        let mut sub: Vec<f32> = Vec::new();
        let mut j = 0;
        while j < len_per_section
            invariant sub.len() == j
            invariant (forall |m: int| 0 <= m < j ==> sub[m] == arr[idx * len_per_section + m])
            decreases len_per_section - j
        {
            sub.push(arr[idx * len_per_section + j]);
            j += 1;
        }
        result.push(sub);
        idx += 1;
    }
    result
}
// </vc-code>

}
fn main() {}