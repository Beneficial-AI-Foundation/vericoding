// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `decreases` clause for `modify_2d_vec_element` and fixed `as nat` compilation error in the code section. */
fn modify_2d_vec_element(arr: &Vec<Vec<u8>>, index1: usize, index2: usize, val: u8) -> (result: Vec<Vec<u8>>) 
    requires
        index1 < arr.len(),
        index2 < arr[index1 as int].len(),
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i && i < arr.len() && i != (index1 as int) ==> result[i as int] == arr[i as int],
        forall|j: int| 0 <= j && j < arr[index1 as int].len() && j != (index2 as int) ==> result[index1 as int][j as int] == arr[index1 as int][j as int],
        result[index1 as int][index2 as int] == val,
{
    let mut new_arr: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant 
            new_arr.len() == i,
            new_arr.len() <= arr.len(),
            forall|k: int| 0 <= k && k < i ==> new_arr[k as int] == arr[k as int],
        decreases (arr.len() - i)
    {
        if i == index1 {
            let mut new_inner_vec: Vec<u8> = Vec::new();
            let mut j = 0;
            while j < arr[i].len()
                invariant
                    new_inner_vec.len() == j,
                    new_inner_vec.len() <= arr[i as int].len(),
                    forall|k: int| 0 <= k && k < j ==> new_inner_vec[k as int] == arr[i as int][k as int],
                decreases (arr[i].len() - j)
            {
                if j == index2 {
                    new_inner_vec.push(val);
                } else {
                    new_inner_vec.push(arr[i][j]);
                }
                j = j + 1;
            }
            new_arr.push(new_inner_vec);
        } else {
            new_arr.push(arr[i].clone());
        }
        i = i + 1;
    }
    new_arr
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
/* code modified by LLM (iteration 5): Fixed `as nat` compilation error by casting `x` to `u8` before passing to `nat::new` because `nat::new` expects a `u8` and not a `nat`.*/
{
    let arr_u8: Vec<Vec<u8>> = arr.into_iter().map(|inner_vec| inner_vec.into_iter().map(|x| x.get() as u8).collect()).collect();
    let result_u8 = modify_2d_vec_element(&arr_u8, index1, index2, val.get() as u8);
    result_u8.into_iter().map(|inner_vec| inner_vec.into_iter().map(|x| nat::new(x as u8)).collect()).collect()
}
// </vc-code>

}
fn main() {}