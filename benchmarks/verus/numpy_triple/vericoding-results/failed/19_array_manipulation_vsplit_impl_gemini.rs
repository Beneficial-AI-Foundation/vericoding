// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed incorrect vstd function names */
proof fn lemma_div_lt(a: nat, b: nat, c: nat)
    requires
        b > 0,
        c > 0,
        a < b * c,
    ensures a / c < b
{
    if a / c >= b {
        let q = a / c;
        vstd::arithmetic::mul::lemma_mul_le_mul_for_nonneg(b as int, q as int, c as int);
        vstd::arithmetic::div_mod::lemma_div_mod_is_refl(a as int, c as int);
        assert(a >= q * c);
        assert(a >= b * c);
        assert(false);
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
/* code modified by LLM (iteration 5): fixed incorrect vstd function names */
{
    let mut result: Vec<Vec<Vec<f32>>> = Vec::new();
    let num_rows_per_split = mat.len() / k;

    let mut split_idx: usize = 0;
    while split_idx < k
        invariant
            0 <= split_idx <= k,
            k > 0,
            mat.len() > 0,
            mat.len() % k == 0,
            forall|i: int| 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
            result.len() == split_idx,
            forall|s_idx: int| 0 <= s_idx < split_idx ==> result[s_idx].len() == mat.len() / k,
            forall|s_idx: int, r_idx: int, c_idx: int|
                0 <= s_idx < split_idx && 0 <= r_idx < mat.len() / k && 0 <= c_idx < mat[0].len() ==> 
                exists|global_row: int| 
                    global_row == s_idx * (mat.len() / k) + r_idx &&
                    0 <= global_row < mat.len() &&
                    result[s_idx][r_idx][c_idx] == mat.view()[global_row][c_idx],
    {
        let mut current_split: Vec<Vec<f32>> = Vec::new();
        let mut row_idx: usize = 0;
        while row_idx < num_rows_per_split
            invariant
                0 <= row_idx <= num_rows_per_split,
                0 <= split_idx < k,
                k > 0,
                mat.len() > 0,
                mat.len() % k == 0,
                forall|i: int| 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
                current_split.len() == row_idx,
                forall|r_idx: int, c_idx: int|
                    0 <= r_idx < row_idx && 0 <= c_idx < mat[0].len() ==> 
                    exists|global_row: int| 
                        global_row == split_idx * num_rows_per_split + r_idx &&
                        0 <= global_row < mat.len() &&
                        current_split.view()[r_idx][c_idx] == mat.view()[global_row][c_idx],
        {
            let global_row = split_idx * num_rows_per_split + row_idx;
            proof {
                vstd::arithmetic::div_mod::lemma_div_by_multiple(mat.len() as nat, k as nat);
            }
            let row_to_add = mat[global_row].clone();
            current_split.push(row_to_add);
            row_idx = row_idx + 1;
        }
        result.push(current_split);
        split_idx = split_idx + 1;
    }

    proof {
        let num_rows_per_split = (mat.len() / k) as nat;
        let mat_len = mat.len() as nat;
        let k_nat = k as nat;
        assert(num_rows_per_split > 0) by {
            assert(mat_len > 0 && k_nat > 0 && mat_len % k_nat == 0);
            if mat_len < k_nat {
                vstd::arithmetic::div_mod::lemma_mod_of_lt(mat_len, k_nat);
                assert(false);
            }
            assert(mat_len >= k_nat);
            vstd::arithmetic::div_mod::lemma_div_is_ge_one(mat_len, k_nat);
            assert(num_rows_per_split >= 1);
        };
        vstd::arithmetic::div_mod::lemma_div_by_multiple(mat_len, k_nat);
        assert forall|orig_row: int| 0 <= orig_row < mat.len() implies
            exists|split_idx: int, row_idx: int|
                0 <= split_idx < k && 0 <= row_idx < mat.len() / k &&
                orig_row == split_idx * (mat.len() / k) + row_idx
        by {
            if 0 <= orig_row < mat.len() {
                let orig_row_nat = orig_row as nat;
                let split_idx_nat = orig_row_nat / num_rows_per_split;
                let row_idx_nat = orig_row_nat % num_rows_per_split;
                
                assert(mat_len == k_nat * num_rows_per_split) by {
                    vstd::arithmetic::mul::lemma_mul_is_commutative(num_rows_per_split as int, k_nat as int);
                };
                
                lemma_div_lt(orig_row_nat, k_nat, num_rows_per_split);
                vstd::arithmetic::div_mod::lemma_mod_is_bounded(orig_row_nat as int, num_rows_per_split as int);
                vstd::arithmetic::div_mod::lemma_div_mod_is_refl(orig_row_nat as int, num_rows_per_split as int);

                assert(orig_row_nat == split_idx_nat * num_rows_per_split + row_idx_nat);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}