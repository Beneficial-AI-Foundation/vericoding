use vstd::prelude::*;

verus! {

// <vc-helpers>
pub open spec fn equal(x: Vec<nat>, y: Vec<nat>) -> bool {
    x.len() == y.len()
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
    let k: int = index1 as int;
    let l: int = index2 as int;

    assert(index1 < arr.len());
    assert(0 <= k && k < arr@.len());
    assert(0 <= l && l < arr@[k].len());

    let arr_len_before = arr.len();
    let row_len_before = arr[index1].len();

    arr[index1][index2] = val;

    assert(arr.len() == arr_len_before);
    assert(arr[index1].len() == row_len_before);
    assert(arr.len() == old(arr).len());

    assert forall |i: int| 0 <= i < arr.len() implies equal(arr[i], old(arr)[i]) by {
        assert(0 <= i && i < arr.len());
        assert(0 <= i && i < old(arr).len());
        if i == k {
            assert(arr[i as usize].len() == old(arr)[i].len());
        } else {
            assert(arr[i as usize].len() == old(arr)[i].len());
        }
    }

    assert forall |i: int, j: int|
        0 <= i < arr.len() && 0 <= j < arr[i].len() && (i != k || j != l)
        implies #[trigger] arr[i][j] == old(arr)[i][j] by {
        assert(0 <= i && i < arr.len());
        assert(0 <= i && i < old(arr).len());
        if i == k {
            assert(arr[i as usize].len() == old(arr)[i].len());
            assert(0 <= j && j < old(arr)[i].len());
            if j != l {
                assert(arr[i as usize][j as usize] == old(arr)[i][j]);
            }
        } else {
            assert(arr[i as usize].len() == old(arr)[i].len());
            assert(0 <= j && j < old(arr)[i].len());
            assert(arr[i as usize][j as usize] == old(arr)[i][j]);
        }
    }

    assert(arr[index1 as int][index2 as int] == val);
}
// </vc-code>

fn main() {}

}