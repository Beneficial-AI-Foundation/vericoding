use vstd::prelude::*;

verus! {

spec fn gcd_int(a: int, b: int) -> int
    recommends a >= 0 && b >= 0
    decreases a + b
    when a >= 0 && b >= 0
{
    if a == 0 { 
        b 
    } else if b == 0 { 
        a 
    } else if a <= b { 
        if b > a { gcd_int(a, b - a) } else { a }
    } else { 
        gcd_int(a - b, b) 
    }
}

fn gcd(a: &Vec<u32>, b: &Vec<u32>) -> (res: Vec<u32>)
    requires 
        a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> gcd_int(a[i] as int, b[i] as int) == res[i] as int,
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|j: int| #![auto] 0 <= j < i ==> gcd_int(a[j] as int, b[j] as int) == res[j] as int,
        decreases a.len() - i
    {
        proof { 
            assert(i < a.len()); 
            assert(0 <= i < a.len());
        }
        let gcd_val = gcd_int_exec(a[i], b[i]);
        res.push(gcd_val);
        i += 1;
    }
    
    res
}

fn gcd_int_exec(a: u32, b: u32) -> (result: u32)
    ensures result as int == gcd_int(a as int, b as int)
    decreases a + b
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a <= b {
        if b > a { 
            gcd_int_exec(a, b - a) 
        } else { 
            a 
        }
    } else {
        gcd_int_exec(a - b, b)
    }
}

}

fn main() {}