// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_nth_implies_all_previous_false(conds: Seq<Seq<bool>>, col_idx: int, chosen_row_idx: int)
    requires
        0 <= chosen_row_idx < conds.len(),
        0 <= col_idx < conds[0].len(),
        conds[chosen_row_idx][col_idx] == true,
        forall|j_prime: int| 0 <= j_prime < chosen_row_idx ==> conds[j_prime][col_idx] == false,
    ensures
        forall|j_prime: int| 0 <= j_prime < chosen_row_idx ==> conds[j_prime][col_idx] == false,
  {
    // The ensures clause is directly satisfied by the requires clause.
  }
// </vc-helpers>

// <vc-spec>
fn select(condlist: Vec<Vec<bool>>, choicelist: Vec<Vec<i8>>, default: i8) -> (result: Vec<i8>)
    requires 
        condlist.len() == choicelist.len(),
        condlist.len() > 0 ==> (forall|i: int| 0 <= i < condlist.len() ==> #[trigger] condlist[i].len() == condlist[0].len()),
        choicelist.len() > 0 ==> (forall|i: int| 0 <= i < choicelist.len() ==> #[trigger] choicelist[i].len() == choicelist[0].len()),
        condlist.len() > 0 && choicelist.len() > 0 ==> condlist[0].len() == choicelist[0].len(),
    ensures
        condlist.len() == 0 ==> result.len() == 0,
        condlist.len() > 0 ==> result.len() == condlist[0].len(),
        forall|i: int| 0 <= i < result.len() ==> {
            (exists|j: int| 0 <= j < condlist.len() && condlist[j][i] == true && 
                #[trigger] result[i] == choicelist[j][i] &&
                (forall|j_prime: int| 0 <= j_prime < j ==> #[trigger] condlist[j_prime][i] == false)) ||
            (forall|j: int| 0 <= j < condlist.len() ==> #[trigger] condlist[j][i] == false && result[i] == default)
        },
// </vc-spec>
// <vc-code>
{
    let num_rows = condlist.len();
    let result_len = if num_rows > 0 { condlist[0].len() } else { 0 };
    let mut result_vec = Vec::new();
    let mut i = 0;

    while i < result_len
        invariant
            0 <= i <= result_len,
            result_vec.len() == i,
            num_rows == 0 ==> result_len == 0,
            num_rows > 0 ==> result_len == condlist[0].len(),
            forall|idx: int| 0 <= idx < i ==> {
                let mut chosen_idx_local: int = -1;
                let mut found_true: bool = false;
                let mut k = 0;
                while k < num_rows
                    invariant
                        0 <= k <= num_rows,
                        0 <= idx < result_len,
                        !found_true ==> forall|j_prime: int| 0 <= j_prime < k ==> condlist.wf_valid() && condlist[j_prime].wf_valid() && condlist[j_prime][idx] == false,
                        found_true ==> (
                            0 <= chosen_idx_local < k && condlist.wf_valid() && condlist[chosen_idx_local].wf_valid() && condlist[chosen_idx_local][idx] == true
                            && forall|j_prime: int| 0 <= j_prime < chosen_idx_local ==> condlist.wf_valid() && condlist[j_prime].wf_valid() && condlist[j_prime][idx] == false
                        ),
                {
                    if condlist[k][idx] && !found_true {
                        chosen_idx_local = k as int;
                        found_true = true;
                    }
                    k = k + 1;
                }

                if found_true {
                    result_vec.view_native()[idx] == choicelist.view_native()[chosen_idx_local][idx]
                } else {
                    result_vec.view_native()[idx] == default
                }
            },
    {
        let mut chosen_row_idx: int = -1;
        let mut found_true_in_col: bool = false;
        let mut j = 0;

        while j < num_rows
            invariant
                0 <= j <= num_rows,
                0 <= i < result_len,
                !found_true_in_col ==> (forall|j_prime: int| 0 <= j_prime < j ==> condlist.wf_valid() && condlist[j_prime].wf_valid() && condlist[j_prime][i] == false),
                found_true_in_col ==> (
                    0 <= chosen_row_idx < j && condlist.wf_valid() && condlist[chosen_row_idx].wf_valid() && condlist[chosen_row_idx][i] == true
                    && (forall|j_prime: int| 0 <= j_prime < chosen_row_idx ==> condlist.wf_valid() && condlist[j_prime].wf_valid() && condlist[j_prime][i] == false)
                ),
        {
            if condlist[j][i] && !found_true_in_col {
                chosen_row_idx = j as int;
                found_true_in_col = true;
            }
            j = j + 1;
        }

        if found_true_in_col {
            result_vec.push(choicelist[chosen_row_idx as usize][i]);
        } else {
            result_vec.push(default);
        }

        i = i + 1;
    }

    result_vec
}
// </vc-code>

}
fn main() {}