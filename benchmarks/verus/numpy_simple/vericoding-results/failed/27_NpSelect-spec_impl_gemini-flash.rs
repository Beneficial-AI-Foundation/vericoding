// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The previous helper was only returning true, making it ineffective. This version correctly uses `ensures b == ( ... )` and an assertion within a proof block to demonstrate the desired property about `condlist` lengths. This ensures that the property is proven when the helper is called. */
fn lemma_nth_implies_nth_plus_one_implies_nth_implies_j_implies_same_len(condlist: Seq<Seq<bool>>, idx: int) -> (b: bool)
    requires
        0 <= idx < condlist.len(),
        forall|i: int, j: int| 0 <= i < condlist.len() && 0 <= j < condlist.len() ==> condlist@[i].len() == condlist@[j].len(),
    ensures
        b == (forall|j: int| 0 <= j < condlist.len() ==> condlist@[idx].len() == condlist@[j].len())
{
    proof {
        assert(forall|j: int| 0 <= j < condlist.len() ==> condlist@[idx].len() == condlist@[j].len());
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn select(condlist: Vec<Vec<bool>>, choicelist: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        condlist@.len() > 0,
        condlist@.len() == choicelist@.len(),
        forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() > 0,
        forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() == choicelist@[i].len(),
        forall|i: int, j: int| 0 <= i < condlist@.len() && 0 <= j < condlist@.len() ==> 
            condlist@[i].len() == condlist@[j].len(),
    ensures
        result@.len() == condlist@[0].len(),
        forall|i: int, j: int| 
            0 <= i < condlist@.len() && 0 <= j < result@.len() && condlist@[i][j] ==> 
            result@[j] == choicelist@[i][j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed a compilation error regarding invariant formatting. The invariant `0 <= j as int < num_cols as int,` had an extra comma, making it `0 <= j as int < num_cols as int,,` which caused the compilation error. Removing the extra comma resolved the issue. */
{
    let num_rows: usize = condlist@.len();
    let num_cols: usize = condlist@[0].len();
    let mut result: Vec<f32> = Vec::new();
    result.reserve(num_cols);

    proof {
        assert(lemma_nth_implies_nth_plus_one_implies_nth_implies_j_implies_same_len(condlist@, 0));
    }

    let mut j: usize = 0;
    while j < num_cols
        invariant
            0 <= j as int && j as int <= num_cols as int,
            j == result@.len(),
            forall|k: int| 0 <= k < j as int ==> (forall|i: int| 0 <= i < num_rows as int && condlist@[i]@[k] ==> result@[k] == choicelist@[i]@[k]),
            forall|i: int, l: int| 0 <= i < num_rows as int && 0 <= l < num_rows as int ==> condlist@[i].len() == condlist@[l].len(),
            num_rows == condlist@.len(),
            num_cols == condlist@[0].len(),
            condlist@.len() == choicelist@.len(),
            forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() > 0,
            forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() == choicelist@[i].len()
        decreases num_cols - j
    {
        let mut found_choice: bool = false;
        let mut choice_value: f32 = 0.0;

        let mut i: usize = 0;
        while i < num_rows
            invariant
                0 <= i as int && i as int <= num_rows as int,
                0 <= j as int && j as int < num_cols as int,
                !found_choice ==> (forall|k: int| 0 <= k < i as int ==> !condlist@[k]@[j as int]),
                found_choice ==> (exists|f_i: int| 0 <= f_i < i as int && condlist@[f_i]@[j as int] && choice_value == choicelist@[f_i]@[j as int]),
                forall|x: int, y: int| 0 <= x < num_rows as int && 0 <= y < num_rows as int ==> condlist@[x].len() == condlist@[y].len(),
                num_rows == condlist@.len(),
                num_cols == condlist@[0].len(),
                condlist@.len() == choicelist@.len(),
                forall|x: int| 0 <= x < condlist@.len() ==> condlist@[x].len() > 0,
                forall|x: int| 0 <= x < condlist@.len() ==> condlist@[x].len() == choicelist@[x].len()
            decreases num_rows - i
        {
            if condlist@[i]@[j] {
                if !found_choice {
                    choice_value = choicelist@[i]@[j];
                    found_choice = true;
                }
            }
            i = i + 1;
        }

        if !found_choice {
            result.push(0.0);
        } else {
            result.push(choice_value);
        }
        j = j + 1;
    }

    result
}
// </vc-code>


}
fn main() {}