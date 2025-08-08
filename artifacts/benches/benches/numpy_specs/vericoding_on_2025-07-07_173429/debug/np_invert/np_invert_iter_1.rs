use vstd::prelude::*;

verus! {

spec fn bitwise_not(x: int) -> int {
    -x - 1
}

fn bitwise_not_impl(x: i32) -> (result: i32)
    ensures result == bitwise_not(x as int),
{
    if x == i32::MIN {
        i32::MAX
    } else {
        -x - 1
    }
}

fn invert(a: &Vec<i32>) -> (res: Vec<i32>)
    requires a.len() >= 0,
    ensures 
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == bitwise_not(a[i] as int),
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            res.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> res[j] == bitwise_not(a[j] as int),
        decreases a.len() - i,
    {
        let val = bitwise_not_impl(a[i]);
        res.push(val);
        i = i + 1;
    }
    
    res
}

} // verus!

fn main() {}