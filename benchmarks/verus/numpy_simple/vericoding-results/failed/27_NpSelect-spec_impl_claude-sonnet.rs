// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to while loop */
fn first_true_index(cond_row: &Vec<bool>) -> (result: usize)
    requires
        cond_row@.len() > 0,
        exists|k: int| 0 <= k < cond_row@.len() && cond_row@[k],
    ensures
        result < cond_row@.len(),
        cond_row@[result as int],
        forall|i: int| 0 <= i < result ==> !cond_row@[i],
{
    let mut idx = 0;
    while idx < cond_row.len()
        invariant
            idx <= cond_row@.len(),
            forall|i: int| 0 <= i < idx ==> !cond_row@[i],
            exists|k: int| idx <= k < cond_row@.len() && cond_row@[k],
        decreases cond_row@.len() - idx
    {
        if cond_row[idx] {
            return idx;
        }
        idx += 1;
    }
    unreached()
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
    /* code modified by LLM (iteration 5): fixed bounds checking with direct proof blocks */
    let n = condlist[0].len();
    let mut result = Vec::with_capacity(n);
    
    let mut j = 0;
    while j < n
        invariant
            j <= n,
            n == condlist@[0].len(),
            result@.len() == j,
            condlist@.len() > 0,
            condlist@.len() == choicelist@.len(),
            forall|k: int| 0 <= k < condlist@.len() ==> condlist@[k].len() == n,
            forall|k: int| 0 <= k < choicelist@.len() ==> choicelist@[k].len() == n,
            forall|col: int, row: int|
                0 <= col < j && 0 <= row < condlist@.len() && condlist@[row][col] ==>
                result@[col] == choicelist@[row][col],
        decreases n - j
    {
        let mut found = false;
        let mut selected_value = 0.0;
        
        let mut i = 0;
        while i < condlist.len()
            invariant
                i <= condlist@.len(),
                j < n,
                condlist@.len() > 0,
                forall|k: int| 0 <= k < condlist@.len() ==> condlist@[k].len() == n,
                forall|k: int| 0 <= k < choicelist@.len() ==> choicelist@[k].len() == n,
                j < condlist@[0].len(),
                !found ==> forall|k: int| 0 <= k < i ==> !condlist@[k][j as int],
                found ==> exists|k: int| 0 <= k < i && 0 <= k < condlist@.len() && 0 <= k < choicelist@.len() && condlist@[k][j as int] && selected_value == choicelist@[k][j as int],
            decreases condlist@.len() - i
        {
            assert(i < condlist@.len());
            assert(condlist@[i as int].len() == n);
            assert(j < n);
            assert(choicelist@[i as int].len() == n);
            
            if condlist[i][j] {
                selected_value = choicelist[i][j];
                found = true;
                
                proof {
                    assert(condlist@[i as int][j as int]);
                    assert(selected_value == choicelist@[i as int][j as int]);
                }
                break;
            }
            i += 1;
        }
        
        result.push(selected_value);
        
        proof {
            assert(forall|row: int|
                0 <= row < condlist@.len() && condlist@[row][j as int] ==>
                selected_value == choicelist@[row][j as int]);
        }
        
        j += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}