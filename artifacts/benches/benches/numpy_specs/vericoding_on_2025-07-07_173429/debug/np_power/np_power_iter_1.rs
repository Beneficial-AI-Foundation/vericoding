use vstd::prelude::*;

verus! {

spec fn pow(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 { 1 } else { base * pow(base, (exp - 1) as nat) }
}

#[verifier::external_body]
fn pow_exec(base: i32, exp: u32) -> (result: i32)
    ensures result as int == pow(base as int, exp as nat)
{
    if exp == 0 {
        1
    } else {
        base * pow_exec(base, exp - 1)
    }
}

fn power(a: &[i32], b: &[u32]) -> (res: Vec<i32>)
    requires a.len() == b.len()
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] as int == pow(a[i] as int, b[i] as nat),
{
    let mut res = Vec::with_capacity(a.len());
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant 
            0 <= idx <= a.len(),
            res.len() == idx,
            a.len() == b.len(),
            forall|j: int| 0 <= j < idx ==> #[trigger] res[j] as int == pow(a[j] as int, b[j] as nat),
        decreases a.len() - idx
    {
        let power_val = pow_exec(a[idx], b[idx]);
        res.push(power_val);
        idx = idx + 1;
    }
    
    res
}

fn main() {}

}