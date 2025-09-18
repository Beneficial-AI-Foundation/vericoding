// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Using Seq for spec functions */
spec fn update_inner_seq(inner: Seq<nat>, index: int, val: nat) -> Seq<nat>
    recommends 0 <= index < inner.len()
{
    inner.update(index, val)
}

spec fn update_outer_seq(arr: Seq<Seq<nat>>, index1: int, new_inner: Seq<nat>) -> Seq<Seq<nat>>
    recommends 0 <= index1 < arr.len()
{
    arr.update(index1, new_inner)
}
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
    /* code modified by LLM (iteration 5): Fixed indexing - use usize for Vec indexing, not int */
    let ghost index1_int: int = index1 as int;
    let ghost index2_int: int = index2 as int;
    
    let inner = arr[index1].clone();
    let ghost new_inner_seq = update_inner_seq(inner@, index2_int, val);
    
    let mut new_inner = inner;
    new_inner.set(index2, val);
    
    let mut result = arr.clone();
    result.set(index1, new_inner);
    
    proof {
        assert(result@[index1_int]@[index2_int] == val);
        assert(result@.len() == arr@.len());
        assert forall|i: int| 0 <= i < arr@.len() && i != index1_int implies result@[i] == arr@[i] by {
            assert(result@[i] == arr@[i]);
        }
        assert forall|j: int| 0 <= j < arr@[index1_int]@.len() && j != index2_int implies result@[index1_int]@[j] == arr@[index1_int]@[j] by {
            assert(result@[index1_int]@[j] == arr@[index1_int]@[j]);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}