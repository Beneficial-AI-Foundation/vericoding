use vstd::prelude::*;

verus! {

// Translation note: Changed from f64 to i32 since Verus doesn't support floating point types yet
fn select(condlist: &Vec<Vec<bool>>, choicelist: &Vec<Vec<i32>>) -> (ret: Vec<i32>)
    requires
        condlist.len() > 0,
        choicelist.len() > 0,
        condlist.len() == choicelist.len(),
        forall|i: int| 0 <= i < condlist.len() ==> #[trigger] condlist[i].len() == condlist[0].len(),
        forall|i: int| 0 <= i < choicelist.len() ==> #[trigger] choicelist[i].len() == condlist[0].len(),
    ensures
        ret.len() == condlist[0].len(),
        forall|i: int, j: int| 
            0 <= i < condlist.len() && 0 <= j < condlist[0].len() && #[trigger] condlist[i][j] ==> 
            ret[j] == choicelist[i][j],
{
    let n = condlist[0].len();
    let mut ret: Vec<i32> = Vec::new();
    
    // Initialize the result vector with zeros
    let mut init_idx = 0;
    while init_idx < n
        invariant 
            init_idx <= n,
            ret.len() == init_idx,
        decreases n - init_idx,
    {
        ret.push(0);
        init_idx += 1;
    }
    
    let mut j = 0;
    while j < n
        invariant 
            j <= n,
            ret.len() == n,
            forall|i: int, k: int| 
                0 <= i < condlist.len() && 0 <= k < j && #[trigger] condlist[i][k] ==> 
                ret[k] == choicelist[i][k],
        decreases n - j,
    {
        let mut i = 0;
        while i < condlist.len()
            invariant 
                i <= condlist.len(),
                j < n,
                ret.len() == n,
                forall|k: int, l: int| 
                    0 <= k < i && 0 <= l < n && #[trigger] condlist[k][l] ==> 
                    ret[l] == choicelist[k][l],
                forall|k: int| 
                    0 <= k < i && #[trigger] condlist[k][j as int] ==> 
                    ret[j as int] == choicelist[k][j as int],
            decreases condlist.len() - i,
        {
            if condlist[i][j] {
                ret.set(j, choicelist[i][j]);
            }
            i += 1;
        }
        j += 1;
    }
    
    ret
}

}