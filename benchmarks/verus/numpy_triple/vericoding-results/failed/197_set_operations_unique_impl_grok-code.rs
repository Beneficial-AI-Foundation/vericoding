// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): defined spec fn for is_sorted */
spec fn is_sorted(s: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s@[i] < s@[j]
}
// </vc-helpers>

// <vc-spec>
fn unique(arr: Vec<i8>) -> (result: Vec<i8>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result@.len() ==> #[trigger] result@[i] < #[trigger] result@[j],

        forall|i: int| 0 <= i < result@.len() ==> exists|j: int| 0 <= j < arr@.len() && #[trigger] result@[i] == #[trigger] arr@[j],

        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> #[trigger] result@[i] != #[trigger] result@[j],

        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < result@.len() && #[trigger] arr@[i] == #[trigger] result@[j],
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): implemented bubble sort and added invariant, used assert with auxiliary function */
let mut result = Vec::new();
if arr.len() <= 0 {
    return result;
}
let mut sorted_vec = arr;
let len = (sorted_vec.len() as int);
let mut i = 0;
while i < len -1
    invariant
        0 <= i <= len -1,
        
    decreases (len - i )
{
    let mut j = 0;
    while j < len - i -1
        
        decreases len - i -1 - j
    {
        if sorted_vec[j as usize] > sorted_vec[(j+1) as usize] {
            let temp = sorted_vec[j as usize];
            sorted_vec = sorted_vec.update(j as usize, sorted_vec[(j+1) as usize]);
            sorted_vec = sorted_vec.update((j+1) as usize, temp);
        }
        j +=1;
    }
    i +=1;
}
/* assert sorted */
assert(is_sorted(sorted_vec@));
result.push(sorted_vec[0]);
let mut k = 1;
while k < len
    
    decreases len - k
{
    if sorted_vec[k as usize] != sorted_vec[(k-1) as usize] {
        result.push(sorted_vec[k as usize]);
    }
    k +=1;
}
result
}
// </vc-code>

}
fn main() {}