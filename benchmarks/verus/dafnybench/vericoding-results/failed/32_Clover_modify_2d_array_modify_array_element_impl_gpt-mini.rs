use vstd::prelude::*;

verus! {

// <vc-helpers>
fn replace_elem_in_vec(row: &Vec<nat>, idx: usize, val: nat) -> Vec<nat>
  requires
    idx < row.len(),
  ensures
    result.len() == row.len(),
    forall|j: int| 0 <= j && j < row.len() as int ==>
        result[j as usize] == if j as usize == idx { val } else { row[j as usize] },
{
    let mut res: Vec<nat> = row.clone();
    res[idx] = val;
    res
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
    let old_arr = arr.clone();
    let n = old_arr.len();
    assert(index1 < n);
    assert(index2 < old_arr[index1].len());

    arr.clear();

    let mut i: usize = 0;
    while i < n
        invariant i <= n;
        invariant arr.len() == i;
        invariant forall|k: int| 0 <= k && k < i as int ==>
            ( if k as usize == index1 {
                equal(arr[k as usize], replace_elem_in_vec(&old_arr[k as usize], index2, val))
              } else {
                equal(arr[k as usize], old_arr[k as usize])
              } );
    {
        if i == index1 {
            let new_row = replace_elem_in_vec(&old_arr[i], index2, val);
            arr.push(new_row);
        } else {
            arr.push(old_arr[i].clone());
        }
        i += 1;
    }

    assert(arr.len() == n);
    assert(arr[index1][index2] == val);
}
// </vc-code>

fn main() {}

}