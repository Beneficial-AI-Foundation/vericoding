use vstd::prelude::*;

verus! {

fn unique_all(arr: &[i32]) -> (ret: Vec<i32>)
    ensures
        ret.len() <= arr.len(),
{
    let mut result: Vec<i32> = Vec::new();
    
    let mut i = 0usize;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result.len() <= i,
        decreases arr.len() - i
    {
        let current_val = arr[i];
        let mut found = false;
        let mut j = 0usize;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
            decreases result.len() - j
        {
            if result[j] == current_val {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            result.push(current_val);
        }
        i += 1;
    }
    
    result
}

}

fn main() {}