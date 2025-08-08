use vstd::prelude::*;

verus! {

fn intersect(a: &[i32], b: &[i32]) -> (ret: Vec<i32>)
    requires a.len() > 0 && b.len() > 0
    ensures 
        ret.len() <= a.len() && ret.len() <= b.len()
{
    let max_size = if a.len() < b.len() { a.len() } else { b.len() };
    let mut temp: Vec<i32> = Vec::with_capacity(max_size);
    
    let mut i = 0;
    while i < a.len()
        invariant 
            i <= a.len(),
            temp.len() <= i,
            temp.len() <= max_size,
        decreases a.len() - i
    {
        // Check if a[i] exists in b
        let mut found = false;
        let mut j = 0;
        while j < b.len()
            invariant 
                j <= b.len(),
                i < a.len(),
                found <==> exists |y: int| 0 <= y < j && a[i as int] == b[y],
            decreases b.len() - j,
        {
            if a[i] == b[j] {
                found = true;
            }
            j = j + 1;
        }
        
        if found {
            // Check if a[i] is already in temp
            let mut already_in_temp = false;
            let mut k = 0;
            while k < temp.len()
                invariant 
                    k <= temp.len(),
                    i < a.len(),
                    already_in_temp <==> exists |z: int| 0 <= z < k && temp[z] == a[i as int],
                decreases temp.len() - k,
            {
                if temp[k] == a[i] {
                    already_in_temp = true;
                }
                k = k + 1;
            }
            
            if !already_in_temp && temp.len() < max_size {
                temp.push(a[i]);
            }
        }
        
        i = i + 1;
    }
    
    let mut ret: Vec<i32> = Vec::with_capacity(temp.len());
    let mut i = 0;
    
    while i < temp.len()
        invariant 
            i <= temp.len(),
            ret.len() == i,
            forall |x: int| 0 <= x < i ==> ret[x] == temp[x],
        decreases temp.len() - i,
    {
        ret.push(temp[i]);
        i = i + 1;
    }
    
    ret
}

fn main() {}

}