use vstd::prelude::*;

verus! {

fn clip(a: &Vec<i32>, min: i32, max: i32) -> (ret: Vec<i32>)
    requires 
        min < max,
    ensures 
        ret.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            #[trigger] ret[i] == 
                if a[i] < min { 
                    min 
                } else if a[i] > max { 
                    max 
                } else { 
                    a[i] 
                },
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant 
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result[j] == 
                    if a[j] < min { 
                        min 
                    } else if a[j] > max { 
                        max 
                    } else { 
                        a[j] 
                    },
        decreases a.len() - i,
    {
        let clipped_value = if a[i] < min {
            min
        } else if a[i] > max {
            max
        } else {
            a[i]
        };
        
        result.push(clipped_value);
        i += 1;
    }
    
    result
}

fn main() {}

}