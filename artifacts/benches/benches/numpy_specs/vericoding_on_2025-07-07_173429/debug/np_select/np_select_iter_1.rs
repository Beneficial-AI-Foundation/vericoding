use vstd::prelude::*;

verus! {

fn select(condlist: Vec<Vec<bool>>, choicelist: Vec<Vec<i32>>) -> (ret: Vec<i32>)
    requires 
        condlist.len() > 0,
        choicelist.len() > 0,
        condlist.len() == choicelist.len(),
        forall|i: int| 0 <= i < condlist.len() ==> 
            condlist[i].len() == condlist[0].len() && 
            choicelist[i].len() == condlist[0].len(),
    ensures 
        ret.len() == condlist[0].len(),
        forall|i: int, j: int| 0 <= i < condlist.len() && 0 <= j < condlist[0].len() ==>
            condlist[i][j] ==> ret[j] == choicelist[i][j],
{
    let mut ret: Vec<i32> = Vec::new();
    
    // Initialize result vector
    for idx in 0..condlist[0].len() 
        invariant ret.len() == idx,
    {
        ret.push(0);
    }
    
    // Process each column
    for j in 0..condlist[0].len()
        invariant
            ret.len() == condlist[0].len(),
            forall|i: int, k: int| 0 <= i < condlist.len() && 0 <= k < j ==> 
                condlist[i][k] ==> ret[k] == choicelist[i][k],
    {
        // Process each row for this column
        for i in 0..condlist.len()
            invariant
                ret.len() == condlist[0].len(),
                forall|k: int| 0 <= k < i ==> 
                    condlist[k][j as int] ==> ret[j as int] == choicelist[k][j as int],
        {
            if condlist[i][j] {
                ret.set(j, choicelist[i][j]);
            }
        }
    }
    
    ret
}

}