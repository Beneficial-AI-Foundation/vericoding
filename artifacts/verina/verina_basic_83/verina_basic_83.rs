use vstd::prelude::*;

verus! {

// Precondition for concat - currently just True (like in Lean)
spec fn concat_precond(a: &Vec<i32>, b: &Vec<i32>) -> bool {
    true
}

// Postcondition for concat  
spec fn concat_postcond(a: &Vec<i32>, b: &Vec<i32>, result: &Vec<i32>) -> bool {
    result.len() == a.len() + b.len()
    && (forall|k: int| 0 <= k < a.len() ==> result[k] == a[k])
    && (forall|k: int| 0 <= k < b.len() ==> result[k + a.len()] == b[k])
}

// The concat function implementation
fn concat(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires 
        concat_precond(a, b),
        a.len() + b.len() <= usize::MAX,
    ensures concat_postcond(a, b, &result),
{
    let a_len = a.len();
    let b_len = b.len();  
    let n = a_len + b_len;
    
    // Create initial array filled with zeros (like Array.mkArray n 0)
    let mut c: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant 
            0 <= i <= n,
            c.len() == i,
            n == a_len + b_len,
            a_len == a.len(),
            b_len == b.len(),
        decreases n - i,
    {
        c.push(0);
        i = i + 1;
    }
    
    // The main loop (recursive loop translated to iterative)
    i = 0;
    while i < n
        invariant 
            0 <= i <= n,
            c.len() == n,
            n == a_len + b_len,
            a_len == a.len(),
            b_len == b.len(),
            forall|k: int| 0 <= k < i ==> {
                if k < a_len {
                    c[k] == a[k]
                } else {
                    c[k] == b[k - a_len]
                }
            },
        decreases n - i,
    {
        let value = if i < a_len {
            a[i]
        } else {
            b[i - a_len]
        };
        c.set(i, value);
        i = i + 1;
    }
    
    c
}

}

fn main() {}