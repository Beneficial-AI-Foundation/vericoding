// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added triggers to quantifiers in loop invariant */
fn find_choice_for_col(condlist: &Vec<Vec<bool>>, choicelist: &Vec<Vec<i8>>, default: i8, i: usize) -> (result: i8)
    requires
        condlist.len() == choicelist.len(),
        condlist.len() > 0,
        (forall|k: int| 0 <= k < condlist.len() ==> #[trigger] condlist@[k].len() == condlist@[0].len()),
        (forall|k: int| 0 <= k < choicelist.len() ==> #[trigger] choicelist@[k].len() == choicelist@[0].len()),
        condlist@[0].len() == choicelist@[0].len(),
        (i as int) < condlist@[0].len(),
    ensures
        (exists|j: int| 0 <= j < condlist.len() && condlist@[j]@[i as int] == true && 
            result == #[trigger] choicelist@[j]@[i as int] &&
            (forall|j_prime: int| 0 <= j_prime < j ==> #[trigger] condlist@[j_prime]@[i as int] == false)) ||
        (forall|j: int| 0 <= j < condlist.len() ==> #[trigger] condlist@[j]@[i as int] == false && result == default)
{
    let num_choices = condlist.len();
    let mut j: usize = 0;
    while j < num_choices
        invariant
            j <= num_choices,
            forall|j_prime: int| 0 <= j_prime < (j as int) ==> condlist@[j_prime]@[i as int] == false,
            // Preconditions for indexing safety
            (i as int) < condlist@[0].len(),
            condlist.len() == choicelist.len(),
            forall|k: int| 0 <= k < condlist.len() ==> #[trigger] condlist@[k].len() == condlist@[0].len(),
            forall|k: int| 0 <= k < choicelist.len() ==> #[trigger] choicelist@[k].len() == choicelist@[0].len(),
            condlist@[0].len() == choicelist@[0].len(),
        decreases num_choices - j
    {
        if condlist[j][i] {
            return choicelist[j][i];
        }
        j = j + 1;
    }
    default
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
/* code modified by LLM (iteration 4): resubmitting previous code, as error was in helper */
{
    if condlist.len() == 0 {
        return Vec::new();
    }

    let M = condlist[0].len();
    let mut result = Vec::with_capacity(M);

    let mut i: usize = 0;
    while i < M
        invariant
            i <= M,
            result.len() == i,
            M == condlist@[0].len(),
            forall|k: int| 0 <= k < i as int ==> {
                (exists|j: int| 0 <= j < condlist.len() && condlist@[j]@[k] == true && 
                    result@[k] == #[trigger] choicelist@[j]@[k] &&
                    (forall|j_prime: int| 0 <= j_prime < j ==> #[trigger] condlist@[j_prime]@[k] == false)) ||
                (forall|j: int| 0 <= j < condlist.len() ==> #[trigger] condlist@[j]@[k] == false && result@[k] == default)
            },
            // Propagate preconditions of `select` for the helper call
            condlist.len() == choicelist.len(),
            condlist.len() > 0 ==> (forall|idx: int| 0 <= idx < condlist.len() ==> #[trigger] condlist@[idx].len() == condlist@[0].len()),
            choicelist.len() > 0 ==> (forall|idx: int| 0 <= idx < choicelist.len() ==> #[trigger] choicelist@[idx].len() == choicelist@[0].len()),
            condlist.len() > 0 && choicelist.len() > 0 ==> condlist@[0].len() == choicelist@[0].len(),
        decreases M - i
    {
        let col_val = find_choice_for_col(&condlist, &choicelist, default, i);
        result.push(col_val);
        i = i + 1;
    }

    result
}

// </vc-code>

}
fn main() {}