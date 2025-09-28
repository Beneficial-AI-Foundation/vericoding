// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
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
/* code modified by LLM (iteration 5): fixed compilation error by correcting indexing syntax in invariant */
    proof {
        assert(arr.len() as nat == k as nat * (arr.len() / k) as nat);
    }
    let sub_len: usize = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::<Vec<f32>>::new();
    let mut i: usize = 0;
    while i < k
        invariant
            i <= k,
            result.len() == i as nat,
            forall|p: int| 0 <= p < i ==> result@[p].len() == sub_len as int,
            forall|p: int, q: int| 
                0 <= p < i && 0 <= q < sub_len as int ==> {
                    let idx = p * (arr.len() / k) as int + q;
                    0 <= idx < arr.len() as int
                },
            forall|p: int, q: int| 
                0 <= p < i && 0 <= q < sub_len as int ==> {
                    let idx = p * (arr.len() / k) as int + q;
                    result@[p]@[q] == arr@[idx]
                }
        decreases k - i
    {
        let mut sub_vec: Vec<f32> = Vec::<f32>::new();
        let mut j: usize = 0;
        while j < sub_len
            invariant
                j <= sub_len,
                sub_vec.len() == j as nat,
                forall|q: int| 0 <= q < j ==> {
                   let idx = i as int * (arr.len() / k) as int + q;
                    0 <= idx < arr.len() as int
                },
                forall|q: int| 0 <= q < j ==> {
                   let idx = i as int * (arr.len() / k) as int + q;
                    sub_vec@[q] == arr@[idx]
                }
            decreases sub_len - j
        {
            let idx: usize = i * (arr.len() / k) + j;
            proof {
                assert(k > 0);
                assert(i >= 0);
                assert(i < k);
                assert(arr.len() % k == 0);
                assert((arr.len() / k) * k == arr.len());
                assert(idx <= (k - 1) * (arr.len() / k) + (sub_len - 1));
                assert((k - 1) * (arr.len() / k) + (arr.len() / k) - 1 == k * (arr.len() / k) - 1);
                assert(arr.len() - 1 >= idx);
                assert(idx as int >= 0);
                assert(idx as int < arr.len() as int);
            }
            sub_vec.push(arr[idx]);
            j += 1;
        }
        result.push(sub_vec);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}