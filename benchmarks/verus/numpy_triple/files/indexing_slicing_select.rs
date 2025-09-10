use vstd::prelude::*;

verus! {

fn select(condlist: Vec<Vec<bool>>, choicelist: Vec<Vec<f32>>, default: f32) -> (result: Vec<f32>)
    requires 
        condlist.len() == choicelist.len(),
        condlist.len() > 0 ==> (forall|i: int| 0 <= i < condlist.len() ==> condlist[i].len() == condlist[0].len()),
        choicelist.len() > 0 ==> (forall|i: int| 0 <= i < choicelist.len() ==> choicelist[i].len() == choicelist[0].len()),
        condlist.len() > 0 && choicelist.len() > 0 ==> condlist[0].len() == choicelist[0].len(),
    ensures
        condlist.len() == 0 ==> result.len() == 0,
        condlist.len() > 0 ==> result.len() == condlist[0].len(),
        forall|i: int| 0 <= i < result.len() ==> {
            (exists|j: int| 0 <= j < condlist.len() && condlist[j][i] == true && 
                result[i] == choicelist[j][i] &&
                (forall|j_prime: int| 0 <= j_prime < j ==> condlist[j_prime][i] == false)) ||
            (forall|j: int| 0 <= j < condlist.len() ==> condlist[j][i] == false && result[i] == default)
        },
{
    assume(false);
    unreached()
}

}
fn main() {}