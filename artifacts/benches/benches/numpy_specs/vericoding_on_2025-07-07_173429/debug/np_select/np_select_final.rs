use vstd::prelude::*;

verus! {

fn select(condlist: Vec<Vec<bool>>, choicelist: Vec<Vec<i64>>) -> (ret: Vec<i64>)
    requires 
        condlist.len() > 0,
        choicelist.len() > 0,
        condlist.len() == choicelist.len(),
        condlist[0].len() > 0,
        forall|i: int| 0 <= i < condlist.len() ==> 
            condlist[i].len() == condlist[0].len() && 
            choicelist[i].len() == condlist[0].len(),
    ensures
        ret.len() == condlist[0].len(),
{
    let cols = condlist[0].len();
    let rows = condlist.len();
    
    // Create result vector
    let mut ret: Vec<i64> = Vec::new();
    
    // Initialize with zeros
    let mut init_idx: usize = 0;
    while init_idx < cols
        invariant
            init_idx <= cols,
            ret.len() == init_idx,
        decreases cols - init_idx
    {
        ret.push(0i64);
        init_idx += 1;
    }
    
    // Main selection logic - nested loops
    let mut j: usize = 0;
    while j < cols
        invariant
            j <= cols,
            ret.len() == cols,
        decreases cols - j  
    {
        let mut i: usize = 0;
        while i < rows
            invariant
                i <= rows,
                j < cols,
                ret.len() == cols,
            decreases rows - i
        {
            // Check bounds and condition before setting
            if i < condlist.len() && j < condlist[i].len() {
                if condlist[i][j] {
                    if i < choicelist.len() && j < choicelist[i].len() {
                        ret.set(j, choicelist[i][j]);
                    }
                }
            }
            i += 1;
        }
        j += 1;
    }
    
    ret
}

fn main() {}

}