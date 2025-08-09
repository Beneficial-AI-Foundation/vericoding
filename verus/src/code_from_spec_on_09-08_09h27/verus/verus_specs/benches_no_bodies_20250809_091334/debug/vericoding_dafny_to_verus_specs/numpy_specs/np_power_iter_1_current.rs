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

fn power(a: &[i32], b: &[u32]) -> (res: Vec<i32>)
    requires a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == pow(a[i] as int, b[i] as nat),
{
    let mut res = Vec::new();
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            res.len() == idx,
            forall|i: int| 0 <= i < idx ==> #[trigger] res[i] == pow(a[i] as int, b[i] as nat),
    {
        let base = a[idx];
        let exp = b[idx];
        let power_result = compute_power(base, exp);
        res.push(power_result);
        idx += 1;
    }
    
    res
}

fn compute_power(base: i32, exp: u32) -> (result: i32)
    ensures result == pow(base as int, exp as nat)
{
    if exp == 0 {
        return 1;
    }
    
    let mut result = 1i32;
    let mut current_exp = 0u32;
    
    while current_exp < exp
        invariant
            current_exp <= exp,
            result == pow(base as int, current_exp as nat),
    {
        result = result.wrapping_mul(base);
        current_exp += 1;
        
        proof {
            assert(result == pow(base as int, current_exp as nat)) by {
                assert(pow(base as int, current_exp as nat) == 
                       base * pow(base as int, (current_exp - 1) as nat));
            }
        }
    }
    
    result
}

fn main() {}

}