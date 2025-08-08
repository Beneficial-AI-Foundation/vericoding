use vstd::prelude::*;

verus! {

spec fn gcd_int(a: int, b: int) -> int
    recommends a >= 0, b >= 0
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd_int(b, a % b)
    }
}

exec fn gcd_int_exec(a: i32, b: i32) -> (result: i32)
    requires a >= 0 && b >= 0
    ensures 
        result >= 0,
        result as int == gcd_int(a as int, b as int),
{
    let mut x = a;
    let mut y = b;
    while y != 0
        invariant 
            x >= 0, 
            y >= 0,
            gcd_int(x as int, y as int) == gcd_int(a as int, b as int),
        decreases y
    {
        let temp = y;
        y = x % y; 
        x = temp;
    }
    x
}

exec fn gcd(a: Vec<i32>, b: Vec<i32>) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] >= 0 && b[i] >= 0,
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> gcd_int(a[i] as int, b[i] as int) == res[i] as int,
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> gcd_int(a[j] as int, b[j] as int) == res[j] as int,
        decreases a.len() - i
    {
        let gcd_val = gcd_int_exec(a[i], b[i]);  
        res.push(gcd_val);
        i = i + 1;
    }
    
    res
}

fn main() {}

}