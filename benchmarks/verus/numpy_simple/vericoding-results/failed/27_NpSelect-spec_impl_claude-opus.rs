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
    let n = condlist.len();
    let m = condlist[0].len();
    let mut result: Vec<f32> = Vec::new();
    let mut j: usize = 0;
    
    while j < m
        invariant
            n == condlist@.len(),
            m == condlist@[0].len(),
            0 <= j <= m,
            result@.len() == j,
            forall|k: int, l: int| 
                0 <= k < condlist@.len() && 0 <= l < j as int && condlist@[k][l] ==> 
                result@[l] == choicelist@[k][l],
        decreases m - j
    {
        let mut i: usize = 0;
        let mut found = false;
        let mut value: f32 = 0.0;
        
        while i < n
            invariant
                n == condlist@.len(),
                m == condlist@[0].len(),
                0 <= i <= n,
                j < m,
                found ==> exists|k: int| 0 <= k < i && condlist@[k][j as int] && value == choicelist@[k][j as int],
                !found ==> forall|k: int| 0 <= k < i ==> !condlist@[k][j as int],
            decreases n - i
        {
            if condlist[i][j] && !found {
                value = choicelist[i][j];
                found = true;
            }
            i = i + 1;
        }
        
        if !found {
            value = 0.0;
        }
        
        result.push(value);
        j = j + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}