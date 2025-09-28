// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn get_sub_array(arr: &Vec<f32>, start: usize, len: usize) -> (sub: Vec<f32>)
    requires
        start + len <= arr.len(),
    ensures
        sub.len() == len,
        sub.view() == arr.view().subrange(start as int, start as int + len as int),
{
    let mut sub: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            sub.len() == i,
            sub.view() == arr.view().subrange(start as int, start as int + i as int),
        decreases len - i
    {
        sub.push(arr[start + i]);
        i = i + 1;
    }
    sub
}
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
{
    let sub_len = arr.len() / sections;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < sections
        invariant
            i <= sections,
            result.len() == i,
            sub_len == arr.len() / sections,
            forall|k: int| 0 <= k < i ==> 
                result[k].view() == arr.view().subrange(k * sub_len, (k + 1) * sub_len),
        decreases sections - i
    {
        let start_index = i * sub_len;
        let sub_arr = get_sub_array(&arr, start_index, sub_len);
        result.push(sub_arr);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}