use vstd::prelude::*;

verus! {

fn piecewise_multi_condition(
    x: &Vec<i32>
) -> (ret: Vec<i32>)
    ensures 
        ret.len() == x.len(),
        forall |i: int| 0 <= i < x.len() ==> {
            if x[i] >= 100 {
                #[trigger] ret[i] == 300  // Third condition matches
            } else if x[i] >= 50 {
                #[trigger] ret[i] == 200  // Second condition matches  
            } else if x[i] >= 0 {
                #[trigger] ret[i] == 100  // First condition matches
            } else {
                #[trigger] ret[i] == 0    // No condition matches, default
            }
        },
{
    let mut ret = Vec::<i32>::new();
    ret.resize(x.len(), 0);
    
    for i in 0..x.len()
        invariant 
            ret.len() == x.len(),
            forall |k: int| 0 <= k < i ==> {
                if x[k] >= 100 {
                    ret[k] == 300
                } else if x[k] >= 50 {
                    ret[k] == 200
                } else if x[k] >= 0 {
                    ret[k] == 100
                } else {
                    ret[k] == 0
                }
            },
    {
        // Evaluate conditions in order (simulating the original piecewise logic)
        if x[i] >= 100 {
            ret.set(i, 300);
        } else if x[i] >= 50 {
            ret.set(i, 200);
        } else if x[i] >= 0 {
            ret.set(i, 100);
        } else {
            ret.set(i, 0);
        }
    }
    
    ret
}

fn main() {}

}