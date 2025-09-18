// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implementation provided in a previous turn and believed to be correct. */
fn create_sub_vec(arr: &Vec<f32>, start: usize, len: usize) -> (sub_vec: Vec<f32>)
    requires
        start + len <= arr.len(),
    ensures
        sub_vec.len() == len,
        forall|i: int| 0 <= i < len ==> #[trigger] sub_vec[i] == arr[start + i],
{
    let mut sub_vec = Vec::new();
    let mut j: usize = 0;
    while j < len
        invariant
            j <= len,
            start + len <= arr.len(),
            sub_vec.len() == j,
            forall|i: int| 0 <= i < j ==> #[trigger] sub_vec[i] == arr[start + i],
        decreases len - j,
    {
        sub_vec.push(arr[start + j]);
        j = j + 1;
    }
    sub_vec
}
// </vc-helpers>

// <vc-spec>
fn split(arr: Vec<f32>, k: usize) -> (result: Vec<Vec<f32>>)
    requires
        k > 0,
        arr.len() % k == 0,
    ensures
        result.len() == k,
        forall|i: int| #[trigger] result[i].len() == (arr.len() / k) ==> (0 <= i < k),
        forall|i: int, j: int| 
            0 <= i < k && 0 <= j < (arr.len() / k) as int ==> {
                let idx = i * (arr.len() / k) as int + j;
                0 <= idx < arr.len() as int && #[trigger] result[i][j] == arr[idx]
            },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proof for integer division property to satisfy loop invariants */
    let sub_len = arr.len() / k;
    proof {
        vstd::arithmetic::lemma_div_mod(arr.len() as nat, k as nat);
    }

    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;

    while i < k
        invariant
            i <= k,
            k > 0,
            arr.len() % k == 0,
            sub_len == arr.len() / k,
            k * sub_len == arr.len(),
            result.len() == i,
            forall|ii: int| 0 <= ii < i ==> #[trigger] result[ii].len() == sub_len,
            forall|ii: int, j: int|
                0 <= ii < i && 0 <= j < sub_len ==> 
                #[trigger] result[ii][j] == arr[ii * sub_len + j],
        decreases k - i,
    {
        let start = i * sub_len;
        assert(start + sub_len <= arr.len());

        let sub_vec = create_sub_vec(&arr, start, sub_len);

        result.push(sub_vec);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}