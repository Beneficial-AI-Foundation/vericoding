use vstd::prelude::*;

verus! {

fn unique_all(arr: &[i32]) -> (ret: Vec<i32>)
    ensures ret.len() <= arr.len()
{
    let mut result: Vec<i32> = Vec::new();
    
    let mut i = 0;
    while i < arr.len()
        invariant 
            i <= arr.len(),
            result.len() <= i,
        decreases arr.len() - i,
    {
        let current = arr[i];
        let mut found = false;
        
        let mut j = 0;
        while j < result.len()
            invariant j <= result.len(),
            decreases result.len() - j,
        {
            if result[j] == current {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        if !found {
            result.push(current);
        }
        
        i = i + 1;
    }
    
    result
}

}

fn main() {}