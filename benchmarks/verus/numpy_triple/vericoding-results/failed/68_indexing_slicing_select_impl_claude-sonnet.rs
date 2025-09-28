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
    /* code modified by LLM (iteration 5): fixed bounds checking and loop invariant maintenance */
    if condlist.len() == 0 {
        return Vec::new();
    }
    
    let result_len = condlist[0].len();
    let mut result = Vec::with_capacity(result_len);
    
    let mut i = 0;
    while i < result_len
        invariant
            i <= result_len,
            result.len() == i,
            condlist.len() > 0,
            result_len == condlist[0].len(),
            forall|k: int| 0 <= k < result.len() ==> {
                (exists|j: int| 0 <= j < condlist.len() && condlist[j as int][k] == true && 
                    result[k] == choicelist[j as int][k] &&
                    (forall|j_prime: int| 0 <= j_prime < j ==> condlist[j_prime as int][k] == false)) ||
                (forall|j: int| 0 <= j < condlist.len() ==> condlist[j as int][k] == false && result[k] == default)
            },
        decreases result_len - i
    {
        let mut j = 0;
        let mut found = false;
        let mut selected_value = default;
        
        while j < condlist.len()
            invariant
                j <= condlist.len(),
                i < result_len,
                !found ==> (forall|j_prime: int| 0 <= j_prime < j ==> condlist[j_prime as int][i as int] == false),
                found ==> (exists|j_sel: int| 0 <= j_sel < j && condlist[j_sel as int][i as int] == true && 
                    selected_value == choicelist[j_sel as int][i as int] &&
                    (forall|j_prime: int| 0 <= j_prime < j_sel ==> condlist[j_prime as int][i as int] == false)),
            decreases condlist.len() - j
        {
            if j < condlist.len() && i < condlist[j as int].len() && condlist[j as int][i as int] {
                selected_value = choicelist[j as int][i as int];
                found = true;
                break;
            }
            j += 1;
        }
        
        result.push(selected_value);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}