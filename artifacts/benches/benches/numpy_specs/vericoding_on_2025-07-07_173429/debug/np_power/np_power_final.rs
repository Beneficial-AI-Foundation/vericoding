use vstd::prelude::*;

verus! {

spec fn pow(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow(base, (exp - 1) as nat)
    }
}

#[verifier::external_body] 
fn compute_power(base: i32, exp: usize) -> (result: i32)
    ensures result == pow(base as int, exp as nat)
{
    let mut result = 1i32;
    let mut i = 0;
    while i < exp {
        result = result * base;
        i = i + 1;
    }
    result
}

fn power(a: &[i32], b: &[usize]) -> (res: Vec<i32>)
    requires a.len() == b.len()
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == pow(a@[i] as int, b@[i] as nat)
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] res[j] == pow(a@[j] as int, b@[j] as nat)
        decreases a.len() - i
    {
        let power_val = compute_power(a[i], b[i]);
        res.push(power_val);
        i = i + 1;
    }
    
    res
}

}

fn main() {}