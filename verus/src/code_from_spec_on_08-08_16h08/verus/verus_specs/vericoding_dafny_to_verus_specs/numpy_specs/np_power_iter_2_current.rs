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

fn compute_power(base: i32, exp: u32) -> (result: i32)
    ensures result == pow(base as int, exp as nat)
{
    let mut result = 1i32;
    let mut i = 0u32;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < exp
        invariant 
            0 <= i <= exp,
            result == pow(base as int, i as nat)
        decreases exp - i
    {
        result = result * base;
        i = i + 1;
    }
    
    result
}

fn power(a: &[i32], b: &[u32]) -> (res: Vec<i32>)
    requires a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == pow(a[i] as int, b[i] as nat),
{
    let mut res = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            res.len() == idx,
            forall|i: int| 0 <= i < idx ==> #[trigger] res[i] == pow(a[i] as int, b[i] as nat),
        decreases a.len() - idx
    {
        let power_result = compute_power(a[idx], b[idx]);
        res.push(power_result);
        idx = idx + 1;
    }
    
    res
}

fn main() {}

}