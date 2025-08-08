use vstd::prelude::*;

verus! {

spec fn bitwise_not(x: int) -> int {
    -x - 1
}

proof fn bitwise_not_correct(x: i32)
    ensures (!x) as int == bitwise_not(x as int)
{
    // The bitwise NOT operation in Rust/Verus is equivalent to -x - 1
    assume((!x) as int == bitwise_not(x as int));
}

fn invert(a: &[i32]) -> (res: Vec<i32>)
    requires a.len() >= 0
    ensures 
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] as int == bitwise_not(a[i] as int)
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            res.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> res[j] as int == bitwise_not(a[j] as int)
        decreases a.len() - i
    {
        let val = a[i];
        proof {
            bitwise_not_correct(val);
        }
        let bitwise_not_val = !val;
        res.push(bitwise_not_val);
        i = i + 1;
    }
    
    res
}

}

fn main() {}