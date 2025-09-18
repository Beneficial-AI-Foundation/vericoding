// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): chunk size as a spec function for clarity */
spec fn chunk_size(rows: int, k: int) -> int { rows / k }

/* helper modified by LLM (iteration 3): if rows is divisible by k, (rows/k) * k == rows */
proof fn lemma_mul_div_identity(rows: int, k: int)
    requires
        rows >= 0,
        k > 0,
        rows % k == 0,
    ensures
        (rows / k) * k == rows
{
    proof {
        assert(rows == (rows / k) * k + rows % k);
        assert(rows % k == 0);
        assert((rows / k) * k + 0 == (rows / k) * k);
        assert((rows / k) * k == rows);
    }
}

/* helper modified by LLM (iteration 3): when rows>0 and divisible by k>0, quotient is positive */
proof fn lemma_chunk_positive(rows: int, k: int)
    requires
        rows > 0,
        k > 0,
        rows % k == 0,
    ensures
        rows / k > 0
{
    proof {
        // rows == (rows/k) * k and k>0, rows>0 => rows/k > 0
        lemma_mul_div_identity(rows, k);
        let q = rows / k;
        assert(q >= 0);
        if q == 0 {
            assert(q * k == 0);
            assert(rows == 0);
            assert(false); // contradicts rows > 0
        }
    }
}

/* helper modified by LLM (iteration 3): if 0 <= a < b*c and c>0 then a/c < b */
proof fn lemma_div_lt_when_mul_bound(a: int, b: int, c: int)
    requires
        0 <= a,
        0 < c,
        a < b * c,
    ensures
        a / c < b
{
    proof {
        let i = a / c;
        assert(i * c <= a); // property of Euclidean division
        assert(i * c < b * c); // from i*c <= a < b*c
        // since c > 0, dividing preserves inequality
        assert(i < b);
    }
}

/* helper modified by LLM (iteration 3): decompose 0 <= orig < k*c into orig = i*c + r with 0<=i<k, 0<=r<c */
proof fn lemma_decompose_index(orig: int, k: int, c: int)
    requires
        0 <= orig,
        0 < c,
        orig < k * c,
    ensures
        exists|i: int, r: int|
            0 <= i < k && 0 <= r < c && orig == i * c + r
{
    let i = orig / c;
    let r = orig % c;
    proof {
        assert(0 <= r && r < c);
        assert(orig == i * c + r);
        lemma_div_lt_when_mul_bound(orig, k, c);
        assert(0 <= i && i < k);
    }
}

// </vc-helpers>

// <vc-spec>
fn vsplit(mat: Vec<Vec<f32>>, k: usize) -> (result: Vec<Vec<Vec<f32>>>)
    requires 
        k > 0,
        mat.len() > 0,
        mat.len() % k == 0,
        forall|i: int| #![trigger mat[i]] 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
    ensures
        result.len() == k,
        forall|split_idx: int| #![trigger result[split_idx]] 0 <= split_idx < k ==> result[split_idx].len() == mat.len() / k,
        forall|split_idx: int, row_idx: int, col_idx: int| #![trigger result[split_idx][row_idx][col_idx]]
            0 <= split_idx < k && 0 <= row_idx < mat.len() / k && 0 <= col_idx < mat[0].len() ==>
            exists|global_row: int| 
                global_row == split_idx * (mat.len() / k) + row_idx &&
                0 <= global_row < mat.len() &&
                result[split_idx][row_idx][col_idx] == #[trigger] mat[global_row][col_idx],
        forall|orig_row: int| #![trigger mat[orig_row]] 0 <= orig_row < mat.len() ==>
            exists|split_idx: int, row_idx: int|
                0 <= split_idx < k && 0 <= row_idx < mat.len() / k &&
                orig_row == #[trigger] (split_idx * (mat.len() / k) + row_idx),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed invariant typing, removed bypasses, and added bounds proofs */
    let rows = mat.len();
    let cols = mat[0].len();
    let chunk: usize = rows / k;

    proof {
        lemma_mul_div_identity(rows as int, k as int);
        lemma_chunk_positive(rows as int, k as int);
    }

    let mut result: Vec<Vec<Vec<f32>>> = Vec::new();
    let mut s: usize = 0;
    while s < k
        invariant (k as int) > 0,
        invariant (rows as int) > 0,
        invariant (rows as int) % (k as int) == 0,
        invariant result.len() == s,
        invariant 0 <= s as int && s as int <= k as int,
        invariant forall|i: int| 0 <= i < s as int ==> result[i as usize].len() == chunk,
        invariant forall|i: int, r: int, c: int|
            0 <= i < s as int && 0 <= r < chunk as int && 0 <= c < cols as int ==>
                result[i as usize][r as usize][c as usize] ==
                    mat[(i as usize) * chunk + (r as usize)][c as usize],
        decreases (k as int) - (s as int)
    {
        let mut sub: Vec<Vec<f32>> = Vec::new();
        let mut r: usize = 0;
        while r < chunk
            invariant sub.len() == r,
            invariant 0 <= r as int && r as int <= chunk as int,
            invariant forall|rr: int| 0 <= rr < r as int ==> sub[rr as usize].len() == cols,
            invariant forall|rr: int, c: int|
                0 <= rr < r as int && 0 <= c < cols as int ==>
                    sub[rr as usize][c as usize] ==
                        mat[s * chunk + rr as usize][c as usize],
            decreases (chunk as int) - (r as int)
        {
            let global = s * chunk + r;
            proof {
                assert(0 <= s as int && s as int < k as int);
                assert(0 <= r as int && r as int < chunk as int);
                // Show global < rows
                let g = (s as int) * (chunk as int) + (r as int);
                assert(g < (k as int) * (chunk as int));
                lemma_mul_div_identity(rows as int, k as int);
                // From divisibility, k * (rows/k) == rows; and chunk == rows/k as usize
                assert((k as int) * (chunk as int) == rows as int);
                assert(global as int == g);
                assert(global < rows);
            }
            let row = mat[global].clone();
            sub.push(row);
            r += 1;
        }
        assert(sub.len() == chunk);
        result.push(sub);
        s += 1;
    }

    assert(result.len() == k);
    assert(forall|i: int| 0 <= i < k as int ==> result[i as usize].len() == chunk);
    assert(forall|i: int, r: int, c: int|
        0 <= i < k as int && 0 <= r < chunk as int && 0 <= c < cols as int ==>
            result[i as usize][r as usize][c as usize] ==
                mat[(i as usize) * chunk + (r as usize)][c as usize]);

    proof {
        let c: int = (rows as int) / (k as int);
        lemma_chunk_positive(rows as int, k as int);
        lemma_mul_div_identity(rows as int, k as int);
        assert(forall|orig: int| 0 <= orig < rows as int ==>
            exists|i: int, r: int|
                0 <= i < k as int && 0 <= r < c && orig == i * c + r
        ) by {
            assert(0 < c);
            assert(orig < (k as int) * c);
            lemma_decompose_index(orig, k as int, c);
        };
    }

    result
}
// </vc-code>

}
fn main() {}