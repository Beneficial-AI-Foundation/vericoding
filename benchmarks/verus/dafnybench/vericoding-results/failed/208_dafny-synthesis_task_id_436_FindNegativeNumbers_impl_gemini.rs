// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_negative(n: int) -> bool {
    n < 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes; helpers are correct for an i64-based implementation, which seems to be the intent despite the spec signature. */
fn is_negative_exec(n: i64) -> (b: bool)
    ensures
        b == is_negative(n as int),
{
    n < 0
}

spec fn negatives_in_prefix(negs: Seq<int>, main_arr: Seq<int>, prefix_len: int) -> bool {
    &&& (forall|k: int| 0 <= k < negs.len() ==> 
            is_negative(negs[k]) && 
            exists|j: int| 0 <= j < prefix_len && main_arr[j] == negs[k])
    &&& (forall|j: int| 0 <= j < prefix_len && is_negative(main_arr[j]) ==> 
            negs.contains(main_arr[j]))
}
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &[int]) -> (negative_list: Vec<int>)
    ensures

        forall|i: int| 0 <= i < negative_list.len() ==> 
            is_negative(negative_list[i]) && exists|j: int| 0 <= j < arr.len() && arr[j] == negative_list[i],

        forall|i: int| 0 <= i < arr.len() && is_negative(arr[i]) ==> 
            exists|j: int| 0 <= j < negative_list.len() && negative_list[j] == arr[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed map closure signatures. This code assumes the function operates on i64, as the spec-based 'int' type leads to unresolvable type contradictions in exec code. */
{
    let mut negative_list: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            negatives_in_prefix(
                negative_list.view().map(|_idx, v| v as int),
                arr.view().map(|_idx, v| v as int),
                i as int
            ),
        decreases arr.len() - i
    {
        let elem = arr[i];
        if is_negative_exec(elem) {
            negative_list.push(elem);
        }
        i = i + 1;
    }
    negative_list
}
// </vc-code>

}
fn main() {}