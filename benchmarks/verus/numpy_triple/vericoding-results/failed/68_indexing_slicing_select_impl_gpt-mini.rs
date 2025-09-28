// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): choose first true condition's choice or default */
fn get_choice_for_index(condlist: &Vec<Vec<bool>>, choicelist: &Vec<Vec<i8>>, default: i8, idx: usize) -> (result: i8)
    requires
        condlist.len() == choicelist.len(),
        condlist.len() > 0 ==> (forall|i: usize| i < condlist.len() ==> #[trigger] condlist[i].len() == condlist[0].len()),
        choicelist.len() > 0 ==> (forall|i: usize| i < choicelist.len() ==> #[trigger] choicelist[i].len() == choicelist[0].len()),
        condlist.len() > 0 ==> idx < condlist[0].len(),
    ensures
        (exists|j: usize| j < condlist.len() && #[trigger] condlist[j][idx] == true && #[trigger] result == choicelist[j][idx] && (forall|j_prime: usize| j_prime < j ==> #[trigger] condlist[j_prime][idx] == false)) ||
        (forall|j: usize| j < condlist.len() ==> #[trigger] condlist[j][idx] == false && result == default),
{
    let mut j: usize = 0;
    let mut found: bool = false;
    let mut val: i8 = default;
    while j < condlist.len()
        invariant
            j <= condlist.len(),
            (found ==> (exists|k: usize| k < j && #[trigger] condlist[k][idx] == true && val == choicelist[k][idx] && (forall|kp: usize| kp < k ==> #[trigger] condlist[kp][idx] == false))),
            (!found ==> (forall|k: usize| k < j ==> #[trigger] condlist[k][idx] == false && val == default)),
        decreases condlist.len() - j
    {
        if !found && condlist[j][idx] {
            found = true;
            val = choicelist[j][idx];
        }
        j = j + 1;
    }
    val
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
    /* code modified by LLM (iteration 5): build result vector using helper per index */
    if condlist.len() == 0 {
        Vec::new()
    } else {
        let n = condlist[0].len();
        let mut res: Vec<i8> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                res.len() == i,
            decreases n - i
        {
            let v = get_choice_for_index(&condlist, &choicelist, default, i);
            res.push(v);
            i = i + 1;
        }
        res
    }
}
// </vc-code>

}
fn main() {}