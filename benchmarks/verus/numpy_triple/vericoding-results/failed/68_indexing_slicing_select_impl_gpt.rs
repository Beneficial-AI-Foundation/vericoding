// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma ensuring equal row lengths under uniform-length precondition */
pub proof fn lemma_row_len_eq<T>(v: &Vec<Vec<T>>, j: int)
    requires
        v.len() > 0,
        0 <= j && j < v.len(),
        forall|i: int| 0 <= i < v.len() ==> #[trigger] v[i].len() == v[0].len(),
    ensures
        v[j].len() == v[0].len(),
{
    assert(v[j].len() == v[0].len());
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
    /* code modified by LLM (iteration 5): implement selection with int-indexed loops and maintain invariant for processed columns */
    if condlist.len() == 0 {
        return Vec::new();
    }

    let rows: int = condlist.len();
    let cols: int = condlist[0].len();
    assert(choicelist.len() == rows);

    let mut result: Vec<i8> = Vec::new();

    // Build result by scanning each column and picking the first true condition row
    let mut i: int = 0;
    while i < cols
        invariant
            0 <= i <= cols,
            result.len() == i,
            forall|k: int| 0 <= k < result.len() ==> {
                (exists|j: int| 0 <= j < rows && #[trigger] condlist[j][k] == true &&
                    #[trigger] result[k] == choicelist[j][k] &&
                    (forall|j2: int| 0 <= j2 < j ==> #[trigger] condlist[j2][k] == false)) ||
                ((forall|j: int| 0 <= j < rows ==> #[trigger] condlist[j][k] == false) && result[k] == default)
            },
        decreases cols - i
    {
        // Find first row j such that condlist[j][i] == true
        let mut found: bool = false;
        let mut found_idx: int = 0;
        let mut j: int = 0;
        while j < rows
            invariant
                0 <= j <= rows,
                (found ==> 0 <= found_idx && found_idx < j && condlist[found_idx][i] == true && (forall|j2: int| 0 <= j2 < found_idx ==> #[trigger] condlist[j2][i] == false)),
                (!found ==> (forall|j2: int| 0 <= j2 < j ==> #[trigger] condlist[j2][i] == false)),
            decreases rows - j
        {
            // Bounds to access condlist[j][i]
            proof { lemma_row_len_eq(&condlist, j); }
            assert(condlist[j].len() == condlist[0].len());
            assert(condlist[0].len() == cols);
            assert(0 <= i && i < condlist[j].len());

            if condlist[j][i] == true {
                if !found {
                    found = true;
                    found_idx = j;
                }
            }
            j = j + 1;
        }

        let chosen: i8 = if found {
            assert(0 <= found_idx && found_idx < rows);
            // Bounds to access choicelist[found_idx][i]
            proof { lemma_row_len_eq(&choicelist, found_idx); }
            assert(choicelist[found_idx].len() == choicelist[0].len());
            assert(condlist[0].len() == choicelist[0].len());
            assert(choicelist[found_idx].len() == cols);
            assert(0 <= i && i < choicelist[found_idx].len());
            choicelist[found_idx][i]
        } else {
            default
        };

        result.push(chosen);
        i = i + 1;
    }

    // Length postcondition
    assert(result.len() == cols);

    result
}
// </vc-code>

}
fn main() {}