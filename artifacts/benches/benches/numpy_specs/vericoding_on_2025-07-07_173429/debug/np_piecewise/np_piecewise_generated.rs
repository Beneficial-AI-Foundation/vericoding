use vstd::prelude::*;

verus! {

fn piecewise(x: Vec<i32>) -> (ret: Vec<i32>)
    ensures
        ret.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {
            if x[i] > 0 {
                ret[i] == x[i]
            } else if x[i] < 0 {
                ret[i] == -1
            } else {
                ret[i] == 0
            }
        },
{
    let mut ret = Vec::new();
    
    // Initialize with default values (mimicking Dafny's array initialization)
    let mut init_i: usize = 0;
    while init_i < x.len()
        invariant 
            ret.len() == init_i,
            init_i <= x.len(),
            forall|j: int| 0 <= j < init_i ==> ret[j] == 0,
        decreases x.len() - init_i
    {
        ret.push(0);
        init_i += 1;
    }
    
    // Main processing loop (mimicking the outer for loop from Dafny)
    let mut i: usize = 0;
    while i < x.len()
        invariant 
            ret.len() == x.len(),
            forall|k: int| 0 <= k < i ==> {
                if x[k] > 0 {
                    ret[k] == x[k]
                } else if x[k] < 0 {
                    ret[k] == -1
                } else {
                    ret[k] == 0
                }
            },
            forall|k: int| i <= k < ret.len() ==> ret[k] == 0,
        decreases x.len() - i
    {
        // Check conditions in order (mimicking inner loop with early break)
        if x[i] > 0 {
            ret.set(i, x[i]);
        } else if x[i] < 0 {
            ret.set(i, -1);
        }
        // If x[i] == 0, no condition matches, ret[i] stays 0
        
        i += 1;
    }
    
    ret
}

fn main() {}

}