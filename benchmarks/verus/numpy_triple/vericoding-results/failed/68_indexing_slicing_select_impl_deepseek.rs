// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed int/nat usage in ghost context */
fn select_one_column(condlist: &Vec<Vec<bool>>, choicelist: &Vec<Vec<i8>>, default: i8, col: nat) -> (result: i8)
    requires
        old(condlist).len() == old(choicelist).len(),
        col < old(condlist[0]).len(),
        forall|i: int| 0 <= i < old(condlist).len() ==> #[trigger] old(condlist)[i].len() == old(condlist[0]).len(),
        forall|i: int| 0 <= i < old(choicelist).len() ==> #[trigger] old(choicelist)[i].len() == old(choicelist[0]).len(),
    ensures
        (exists|j: int| 0 <= j < old(condlist).len() && old(condlist)[j][col] == true && 
            result == old(choicelist)[j][col] &&
            (forall|j_prime: int| 0 <= j_prime < j ==> #[trigger] old(condlist)[j_prime][col] == false)) ||
        (forall|j: int| 0 <= j < old(condlist).len() ==> #[trigger] old(condlist)[j][col] == false && result == default)
{
    let mut j: usize = 0;
    let len: usize = condlist.len();

    while j < len
        invariant
            j <= len,
            forall|k: int| 0 <= k < j ==> #[trigger] condlist[k as usize][col] == false
    {
        if condlist[j][col] {
            return choicelist[j][col];
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
/* code modified by LLM (iteration 5): Fixed int/nat usage in ghost context */
{
    if condlist.len() == 0 {
        Vec::new()
    } else {
        let n: usize = condlist[0].len();
        let mut result = Vec::<i8>::new();
        let mut i: usize = 0;
        
        while i < n
            invariant
                i <= n,
                result.len() == i,
                forall|k: nat| k < i ==> {
                    (exists|j: int| 0 <= j < condlist.len() && condlist[j][k] == true && 
                        #[trigger] result[k] == choicelist[j][k] &&
                        (forall|j_prime: int| 0 <= j_prime < j ==> #[trigger] condlist[j_prime][k] == false)) ||
                    (forall|j: int| 0 <= j < condlist.len() ==> #[trigger] condlist[j][k] == false && result[k] == default)
                }
        {
            let value = select_one_column(&condlist, &choicelist, default, i);
            result.push(value);
            i = i + 1;
        }
        
        result
    }
}
// </vc-code>

}
fn main() {}