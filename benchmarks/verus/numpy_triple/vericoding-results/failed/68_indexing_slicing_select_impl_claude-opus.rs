// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 4): added decreases clause to both loops */
    if condlist.len() == 0 {
        return Vec::new();
    }
    
    let n = condlist[0].len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> {
                (exists|j: int| 0 <= j < condlist.len() as int && condlist@[j]@[k] == true && 
                    #[trigger] result@[k] == choicelist@[j]@[k] &&
                    (forall|j_prime: int| 0 <= j_prime < j ==> #[trigger] condlist@[j_prime]@[k] == false)) ||
                (forall|j: int| 0 <= j < condlist.len() as int ==> #[trigger] condlist@[j]@[k] == false && result@[k] == default)
            },
        decreases n - i
    {
        let mut j: usize = 0;
        let mut found = false;
        let mut value = default;
        
        while j < condlist.len()
            invariant
                0 <= j <= condlist.len(),
                found ==> exists|jj: int| 0 <= jj < j as int && condlist@[jj]@[i as int] == true && value == choicelist@[jj]@[i as int] &&
                    (forall|j_prime: int| 0 <= j_prime < jj ==> condlist@[j_prime]@[i as int] == false),
                !found ==> forall|jj: int| 0 <= jj < j as int ==> condlist@[jj]@[i as int] == false,
            decreases condlist.len() - j
        {
            if !found && condlist[j][i] {
                found = true;
                value = choicelist[j][i];
            }
            j = j + 1;
        }
        
        result.push(value);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}