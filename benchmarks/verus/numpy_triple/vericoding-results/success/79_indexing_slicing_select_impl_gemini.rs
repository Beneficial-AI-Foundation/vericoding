// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added missing decreases clause to the loop */
fn find_first_true_row(i: usize, condlist: &Vec<Vec<bool>>) -> (j: usize)
    requires
        condlist.len() > 0 ==> (forall|k: int| #![trigger condlist[k]] 0 <= k < condlist.len() ==> condlist[k].len() == condlist[0].len()),
        condlist.len() > 0 ==> (i as nat) < condlist[0].len(),
    ensures
        0 <= j <= condlist.len(),
        (j < condlist.len() && condlist[j as int][i as int] && (forall|k: int| 0 <= k < (j as int) ==> !condlist[k][i as int])) ||
        (j == condlist.len() && (forall|k: int| 0 <= k < condlist.len() ==> !condlist[k][i as int])),
{
    let mut j: usize = 0;
    while j < condlist.len()
        invariant
            0 <= j <= condlist.len(),
            forall|k: int| 0 <= k < (j as int) ==> !condlist[k][i as int],
            condlist.len() > 0 ==> (forall|k_inv: int| #![trigger condlist[k_inv]] 0 <= k_inv < condlist.len() ==> condlist[k_inv].len() == condlist[0].len()),
            condlist.len() > 0 ==> (i as nat) < condlist[0].len(),
        decreases condlist.len() - j,
    {
        if condlist[j][i] {
            return j;
        }
        j = j + 1;
    }
    j
}
// </vc-helpers>

// <vc-spec>
fn select(condlist: Vec<Vec<bool>>, choicelist: Vec<Vec<f32>>, default: f32) -> (result: Vec<f32>)
    requires 
        condlist.len() == choicelist.len(),
        condlist.len() > 0 ==> (forall|i: int| #![trigger condlist[i]] 0 <= i < condlist.len() ==> condlist[i].len() == condlist[0].len()),
        choicelist.len() > 0 ==> (forall|i: int| #![trigger choicelist[i]] 0 <= i < choicelist.len() ==> choicelist[i].len() == choicelist[0].len()),
        condlist.len() > 0 && choicelist.len() > 0 ==> condlist[0].len() == choicelist[0].len(),
    ensures
        condlist.len() == 0 ==> result.len() == 0,
        condlist.len() > 0 ==> result.len() == condlist[0].len(),
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            (exists|j: int| 0 <= j < condlist.len() && condlist[j][i] == true && 
                result[i] == choicelist[j][i] &&
                (forall|j_prime: int| 0 <= j_prime < j ==> condlist[j_prime][i] == false)) ||
            (forall|j: int| 0 <= j < condlist.len() ==> condlist[j][i] == false && result[i] == default)
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added missing decreases clause to the loop */
    if condlist.len() == 0 {
        return Vec::new();
    }

    let n = condlist[0].len();
    let mut result: Vec<f32> = Vec::with_capacity(n);
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            condlist.len() == choicelist.len(),
            condlist.len() > 0 ==> (forall|k: int| #![trigger condlist[k]] 0 <= k < condlist.len() ==> condlist[k].len() == condlist[0].len()),
            choicelist.len() > 0 ==> (forall|k: int| #![trigger choicelist[k]] 0 <= k < choicelist.len() ==> choicelist[k].len() == choicelist[0].len()),
            condlist.len() > 0 && choicelist.len() > 0 ==> condlist[0].len() == choicelist[0].len(),
            condlist.len() > 0 ==> condlist[0].len() == n,
            result.len() == i,
            forall|k: int| #![trigger result[k]] 0 <= k < (i as int) ==> {
                (exists|j: int| 0 <= j < condlist.len() && condlist[j][k] && 
                    result[k] == choicelist[j][k] &&
                    (forall|j_prime: int| 0 <= j_prime < j ==> !condlist[j_prime][k])) ||
                (forall|j: int| 0 <= j < condlist.len() ==> !condlist[j][k] && result[k] == default)
            },
        decreases n - i,
    {
        let j = find_first_true_row(i, &condlist);
        let val = if j < condlist.len() {
            choicelist[j][i]
        } else {
            default
        };
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}