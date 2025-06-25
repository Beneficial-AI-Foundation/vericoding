pub fn modify_array_element(arr: &mut [&mut [nat]], index1: nat, index2: nat, val: nat)
    requires
        index1 < arr.len(),
        index2 < arr[index1 as int].len(),
        forall|i: nat, j: nat| i < arr.len() && j < arr.len() && i != j ==> arr[i as int] != arr[j as int],
    ensures
        forall|i: nat| 0 <= i < arr.len() ==> arr[i as int] == old(arr)[i as int],
        forall|i: nat, j: nat| 0 <= i < arr.len() && 0 <= j < arr[i as int].len() && (i != index1 || j != index2) ==> arr[i as int][j as int] == old(arr)[i as int][j as int],
        arr[index1 as int][index2 as int] == val,
{
}