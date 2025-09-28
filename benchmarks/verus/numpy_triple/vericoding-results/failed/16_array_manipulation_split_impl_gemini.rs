// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): fixed compilation errors by using correct vstd lemma names */
{
    let chunk_size = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;

    while i < k
        invariant
            0 <= i <= k,
            k > 0,
            arr.len() % k == 0,
            chunk_size == arr.len() / k,
            result.len() == i,
            forall|m: int| 0 <= m < i as int ==> #[trigger] result[m].len() == chunk_size as int,
            forall|m: int, j: int|
                (0 <= m < i as int && 0 <= j < chunk_size as int) ==> {
                    let idx = m * (chunk_size as int) + j;
                    idx < arr.len() as int && #[trigger] result[m][j] == arr[idx as usize]
                },
        decreases k - i
    {
        let start = i * chunk_size;
        let end = start + chunk_size;

        proof {
            assert(end <= arr.len()) by {
                vstd::arithmetic::div_mod::lemma_div_is_divisible(arr.len() as nat, k as nat);
                assert(chunk_size * k == arr.len());
                vstd::arithmetic::mul::lemma_mul_le_mul_of_nonneg((i + 1) as int, k as int, chunk_size as int);
                assert((i + 1) * chunk_size <= k * chunk_size);
            };
        }

        let sub_vec = arr.subrange(start, end);
        result.push(sub_vec);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}