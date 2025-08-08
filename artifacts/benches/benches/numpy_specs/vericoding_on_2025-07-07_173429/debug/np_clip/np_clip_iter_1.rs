use vstd::prelude::*;

verus! {

fn clip(a: &Vec<i32>, min: i32, max: i32) -> (ret: Vec<i32>)
    requires
        min < max,
    ensures
        ret.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            #[trigger] a[i] == a[i] && #[trigger] ret[i] == ret[i] ==>
            if a[i] < min { ret[i] == min } 
            else if a[i] > max { ret[i] == max } 
            else { ret[i] == a[i] },
{
    let mut ret = Vec::with_capacity(a.len());
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] a[j] == a[j] && #[trigger] ret[j] == ret[j] ==>
                if a[j] < min { ret[j] == min } 
                else if a[j] > max { ret[j] == max } 
                else { ret[j] == a[j] },
        decreases a.len() - i,
    {
        let a_val = a[i];
        let value = if a_val < min {
            min
        } else if a_val > max {
            max
        } else {
            a_val
        };
        ret.push(value);
        i += 1;
    }
    
    ret
}

fn main() {}

}