use vstd::prelude::*;

verus! {

fn clip(a: &Vec<i32>, min: i32, max: i32) -> (ret: Vec<i32>)
    requires min < max
    ensures 
        ret.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            if a[i] < min { ret[i] == min } 
            else if a[i] > max { ret[i] == max }
            else { ret[i] == a[i] }
{
    let mut ret = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            ret.len() == i,
            forall|j: int| 0 <= j < i ==> 
                if a[j] < min { ret[j] == min }
                else if a[j] > max { ret[j] == max }
                else { ret[j] == a[j] }
        decreases a.len() - i
    {
        if a[i] < min {
            ret.push(min);
        } else if a[i] > max {
            ret.push(max);
        } else {
            ret.push(a[i]);
        }
        
        i += 1;
    }
    
    ret
}

}

fn main() {}