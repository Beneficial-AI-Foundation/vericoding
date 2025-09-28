// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove linear index within total range */
proof fn lemma_idx_lt_total(i: int, j: int, part: int, k: int)
    requires
        0 <= i < k,
        0 <= j < part,
        0 < part,
    ensures
        0 <= i * part + j,
        i * part + j < k * part,
{
    // Lower bound
    assert(i * part <= i * part + j);
    assert(0 <= i * part);
    assert(0 <= j);
    assert(0 <= i * part + j);

    // Upper bound: j < part ==> i*part + j < (i+1)*part
    assert(i * part + j < i * part + part);
    assert(i * part + j < (i + 1) * part);

    // Since i < k, i+1 <= k
    assert(i + 1 <= k);

    // Monotonicity of multiplication by positive part
    assert((i + 1) * part <= k * part);

    // Chain the inequalities
    assert(i * part + j < k * part);
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
    /* code modified by LLM (iteration 2): implement split using usize loops; prove bounds and mapping with ints in proof blocks */
    let part_len: usize = arr.len() / k;
    let mut res: Vec<Vec<f32>> = Vec::new();

    proof {
        assert(arr.len() % k == 0);
        assert(arr.len() as int == (arr.len() / k) as int * (k as int) + (arr.len() % k) as int);
        assert((arr.len() % k) as int == 0);
        assert(arr.len() as int == (part_len as int) * (k as int));
    }

    let mut i: usize = 0;
    while i < k
        invariant
            0 <= i as int <= k as int,
            res.len() == i,
            forall|ii: int|
                0 <= ii < i as int ==> res[ii].len() == part_len,
            forall|ii: int, jj: int|
                0 <= ii < i as int && 0 <= jj < part_len as int ==> {
                    let idx0 = ii * (part_len as int) + jj;
                    0 <= idx0 < arr.len() as int && #[trigger] res[ii][jj] == arr[idx0]
                },
        decreases (k as int) - (i as int)
    {
        let mut chunk: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < part_len
            invariant
                0 <= j as int <= part_len as int,
                chunk.len() == j,
                forall|jj: int|
                    0 <= jj < j as int ==> {
                        let idx0 = (i as int) * (part_len as int) + jj;
                        0 <= idx0 < arr.len() as int && #[trigger] chunk[jj] == arr[idx0]
                    },
            decreases (part_len as int) - (j as int)
        {
            let idx_usize: usize = i * part_len + j;
            proof {
                let i_i = i as int;
                let j_i = j as int;
                let part_i = part_len as int;
                let k_i = k as int;
                // From preconditions, arr.len() == k * part_len (as ints)
                assert(arr.len() as int == (part_len as int) * (k as int));
                assert(0 <= i_i < k_i);
                assert(0 <= j_i < part_i);
                assert(part_len > 0 ==> 0 < part_i);
                if part_len > 0 {
                    lemma_idx_lt_total(i_i, j_i, part_i, k_i);
                }
                let idx_i = i_i * part_i + j_i;
                assert(0 <= idx_i < arr.len() as int);
                // Relate usize arithmetic to int arithmetic
                assert((i * part_len + j) as int == (i as int) * (part_len as int) + (j as int));
                assert(idx_usize as int == idx_i);
            }
            let val = arr[idx_usize];
            chunk.push(val);
            j = j + 1;
        }
        proof {
            assert(chunk.len() == part_len);
            // After push, the new element is at index i
        }
        res.push(chunk);
        i = i + 1;
    }

    res
}
// </vc-code>

}
fn main() {}