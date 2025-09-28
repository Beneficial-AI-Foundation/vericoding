use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
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
    // Get a mutable reference to the inner vector and modify it in place
    let inner_vec = &mut arr[index1];
    inner_vec.set(index2, val);
    
    // Prove postconditions
    assert(arr.len() == old(arr).len());
    assert(arr[index1 as int][index2 as int] == val);
    
    // Prove that all vectors maintain the same identity
    assert forall|i: int| 0 <= i < arr.len() implies equal(arr[i], old(arr)[i]) by {
        // All vectors maintain their identity since we modified in-place
        assert(equal(arr[i], old(arr)[i]));
    }
    
    // Prove that all elements are preserved except the modified one
    assert forall|i: int, j: int| 
        0 <= i < arr.len() && 0 <= j < arr[i].len() && (i != index1 || j != index2)
        implies arr[i][j] == old(arr)[i][j] by {
        if i == index1 && j != index2 {
            // For the modified vector at index1, elements other than index2 are preserved
            assert(arr[i][j] == old(arr)[i][j]);
        } else if i != index1 {
            // For all other vectors, they remain completely unchanged
            assert(arr[i][j] == old(arr)[i][j]);
        }
    }
}
// </vc-code>

fn main() {}

}