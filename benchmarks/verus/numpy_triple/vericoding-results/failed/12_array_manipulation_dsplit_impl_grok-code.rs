// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
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
/* code modified by LLM (iteration 5): remove unnecessary proof block with assert as invariants ensure the range condition */
{
    let sub_len = arr.len() / sections;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < sections
        invariant
            result.len() as int == i as int,
            forall |k: int| 0 <= k < i as int ==> result[k].len() as int == sub_len as int,
            forall |k: int, m: int| 0 <= k < i as int && 0 <= m < sub_len as int ==> result[k][m] == arr[k * (sub_len as int) + m],
        decreases sections - i
    {
        let mut sub: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < sub_len
            invariant
                sub.len() as int == j as int,
                forall |n: int| 0 <= n < j as int ==> sub[n] == arr[(i as int) * (sub_len as int) + n],
            decreases sub_len - j
        {
            let index = i * sub_len + j;
            sub.push(arr[index]);
            j = j + 1;
        }
        result.push(sub);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}