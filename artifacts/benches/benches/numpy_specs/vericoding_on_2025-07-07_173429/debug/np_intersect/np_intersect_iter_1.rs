use vstd::prelude::*;

verus! {

fn intersect(a: &[i32], b: &[i32]) -> (ret: Vec<i32>)
    requires 
        a.len() >= 1,
        b.len() >= 1
    ensures 
        ret.len() < a.len(),
        ret.len() < b.len()
{
    let max_size = if a.len() <= b.len() { a.len() - 1 } else { b.len() - 1 };
    let mut temp = Vec::with_capacity(max_size);
    
    let mut i = 0;
    while i < a.len() && temp.len() < max_size
        invariant
            0 <= i <= a.len(),
            temp.len() <= max_size,
            max_size < a.len(),
            max_size < b.len()
        decreases a.len() - i
    {
        // Check if a[i] exists in b
        let mut found_in_b = false;
        let mut j = 0;
        while j < b.len() && !found_in_b
            invariant
                0 <= j <= b.len(),
                i < a.len()
            decreases b.len() - j
        {
            if a[i] == b[j] {
                found_in_b = true;
            }
            j += 1;
        }
        
        if found_in_b {
            // Check if a[i] is already in temp
            let mut found_in_temp = false;
            let mut k = 0;
            while k < temp.len() && !found_in_temp
                invariant
                    0 <= k <= temp.len(),
                    i < a.len()
                decreases temp.len() - k
            {
                if temp[k] == a[i] {
                    found_in_temp = true;
                }
                k += 1;
            }
            
            if !found_in_temp && temp.len() < max_size {
                temp.push(a[i]);
            }
        }
        i += 1;
    }
    
    temp
}

fn main() {}

}