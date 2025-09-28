// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix predicate syntax with exclamation mark */
predicate! equal_lengths<T, U>(vec: Vec<T>, vec2: Vec<U>) {
    vec@.len() == vec2@.len()
}

predicate! same_inner_lengths(condlist: Vec<Vec<bool>>) {
    forall|i: int, j: int| 0 <= i < condlist@.len() && 0 <= j < condlist@.len() ==> 
        condlist@[i].len() == condlist@[j].len()
}

predicate! valid_choice_at_index(condlist: Vec<Vec<bool>>, choicelist: Vec<Vec<f32>>, result: Vec<f32>, i: int) {
    forall|j: int| 0 <= j < result@.len() && condlist@[i][j] ==> result@[j] == choicelist@[i][j]
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
{
    /* code modified by LLM (iteration 5): Fixed compilation error with predicate syntax */
    let n = condlist@.len();
    let m = condlist@[0].len();
    let mut result = Vec::new();
    let mut j = 0;
    while j < m
        invariant
            0 <= j <= m,
            result@.len() == j
    {
        let mut current_choice: f32 = 0.0;
        let mut found = false;
        let mut i = 0;
        while i < n
            invariant
                0 <= i <= n,
                !found ==> forall|k: int| 0 <= k < i ==> !condlist@[k][j],
                found ==> exists|k: int| 0 <= k < i && condlist@[k][j] && current_choice == choicelist@[k][j]
        {
            if condlist[i][j] {
                current_choice = choicelist[i][j];
                found = true;
            }
            i += 1;
        }
        result.push(current_choice);
        j += 1;
    }
    result
}
// </vc-code>


}
fn main() {}