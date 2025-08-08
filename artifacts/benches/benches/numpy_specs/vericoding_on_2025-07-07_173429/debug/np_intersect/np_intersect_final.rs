use vstd::prelude::*;

verus! {

fn intersect(a: &[i32], b: &[i32]) -> (ret: Vec<i32>)
    requires a.len() > 0 && b.len() > 0
    ensures ret.len() <= a.len() && ret.len() <= b.len()
{
    let max_len = if a.len() < b.len() { a.len() } else { b.len() };
    let mut temp: Vec<i32> = Vec::with_capacity(max_len);
    
    let mut i = 0usize;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            temp.len() <= max_len,
            temp.len() <= i
        decreases a.len() - i
    {
        let mut found = false;
        let mut j = 0usize;
        while j < b.len()
            invariant 
                0 <= j <= b.len(),
                i < a.len()
            decreases b.len() - j
        {
            if a[i] == b[j] {
                found = true;
                break;
            }
            j += 1;
        }
        
        if found {
            let mut already_in_temp = false;
            let mut k = 0usize;
            while k < temp.len()
                invariant 
                    0 <= k <= temp.len(),
                    i < a.len()
                decreases temp.len() - k
            {
                if temp[k] == a[i] {
                    already_in_temp = true;
                    break;
                }
                k += 1;
            }
            
            if !already_in_temp && temp.len() < max_len {
                temp.push(a[i]);
            }
        }
        i += 1;
    }
    
    temp
}

fn main() {}

}