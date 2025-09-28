// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): added decreases clauses to loops and removed incorrect proof block */
    let M = condlist[0].len();
    let N = condlist.len();

    let mut result = choicelist[0].clone();

    let mut i = 1;
    while i < N
        invariant
            1 <= i <= N,
            result@.len() == M as int,
            forall|row: int, col: int|
                0 <= row < (i as int) && 0 <= col < (M as int) && condlist@[row]@[col] ==> result@[col] == choicelist@[row]@[col],
        decreases (N - i) as nat
    {
        let mut j = 0;
        while j < M
            invariant
                0 <= j <= M,
                1 <= i < N,
                result@.len() == M as int,
                forall|row: int, col: int|
                    (0 <= row < (i as int) && (j as int) <= col < (M as int) && condlist@[row]@[col] ==> result@[col] == choicelist@[row]@[col]),
                forall|row: int, col: int|
                    (0 <= row <= (i as int) && 0 <= col < (j as int) && condlist@[row]@[col] ==> result@[col] == choicelist@[row]@[col]),
            decreases (M - j) as nat
        {
            if condlist[i][j] {
                result.set(j, choicelist[i][j]);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}