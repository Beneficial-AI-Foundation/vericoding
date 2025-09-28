use vstd::prelude::*;

verus! {

// <vc-helpers>
fn equal<T: std::cmp::PartialEq>(arr1: &Vec<T>, arr2: &Vec<T>) -> bool {
    if arr1.len() != arr2.len() {
        false
    } else {
        let mut i = 0;
        #[verifier::loop_invariant_param(arr1, arr2)]
        while i < arr1.len()
            invariant
                0 <= i <= arr1.len(),
                arr1.len() == arr2.len(),
                forall|k: int| 0 <= k < i ==> arr1[k] == arr2[k],
        {
            if arr1[i] != arr2[i] {
                return false;
            }
            i = i + 1;
        }
        true
    }
}
// </vc-helpers>

// <vc-spec>
fn modify_array_element(arr: &mut Vec<Vec<nat>>, index1: usize, index2: usize, val: nat)
  requires
      index1 < old(arr).len(),
      index2 < old(arr)[index1 as int].len(),
      forall|i: int, j: int| 
          0 <= i < old(arr).len() && 0 <= j < old(arr).len() && i != j ==> 
          !equal(old(arr)[i], old(arr)[j]),
  ensures
      arr.len() == old(arr).len(),
      forall|i: int| 0 <= i < arr.len() ==> equal(arr[i], old(arr)[i]),
      forall|i: int, j: int| 
          0 <= i < arr.len() && 0 <= j < arr[i].len() && 
          (i != index1 || j != index2) ==> 
          arr[i][j] == old(arr)[i][j],
      arr[index1 as int][index2 as int] == val,
// </vc-spec>
// <vc-code>
{
    assert(index1 < arr.len());
    let idx1_int: int = index1 as int; 
    assert(index2 < arr[idx1_int].len());
    arr[index1][index2] = val;
}
// </vc-code>

fn main() {}

}