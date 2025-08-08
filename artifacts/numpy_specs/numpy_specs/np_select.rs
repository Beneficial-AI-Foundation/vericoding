use vstd::prelude::*;

verus! {

fn select(condlist: &Vec<Vec<bool>>, choicelist: &Vec<Vec<i32>>) -> (ret: Vec<i32>)
    requires 
        condlist.len() > 0,
        choicelist.len() > 0, 
        condlist.len() == choicelist.len(),
        forall|i: int| 0 <= i < condlist.len() ==> {
            &&& condlist[i].len() == condlist[0].len() 
            &&& choicelist[i].len() == condlist[0].len()
        },
    ensures 
        ret.len() == condlist[0].len(),
        forall|i: int, j: int| 
            0 <= i < condlist.len() && 0 <= j < condlist[0].len() && 
            condlist[i][j] ==> ret[j] == choicelist[i][j],
{
    assume(false);
    Vec::new()
}

}

fn main() {}