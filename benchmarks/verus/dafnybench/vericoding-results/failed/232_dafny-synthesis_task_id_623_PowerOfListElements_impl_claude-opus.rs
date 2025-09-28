use vstd::prelude::*;

verus! {

spec fn power(base: int, exponent: int) -> int
    recommends exponent >= 0
    decreases exponent
{
    if exponent <= 0 { 1 } else { base * power(base, exponent - 1) }
}

// <vc-helpers>
// Helper function to compute power iteratively
fn compute_power(base: i32, exponent: u32) -> (result: i32)
    ensures result == power(base as int, exponent as int)
{
    let mut result: i32 = 1;
    let mut i: u32 = 0;
    
    while i < exponent
        invariant
            0 <= i <= exponent,
            result == power(base as int, i as int),
        decreases exponent - i,
    {
        let old_result = result;
        let old_i = i;
        
        result = result * base;
        i = i + 1;
        
        assert(power(base as int, (old_i + 1) as int) == base * power(base as int, old_i as int)) by {
            reveal(power);
        }
        assert(result == power(base as int, i as int));
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn power_of_list_elements(l: Vec<i32>, n: u32) -> (result: Vec<i32>)
    ensures 
        result.len() == l.len(),
        forall|i: int| #![auto] 0 <= i < l.len() ==> result[i] == power(l[i] as int, n as int),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            result.len() == i,
            forall|j: int| #![trigger result@[j]] 0 <= j < i ==> result@[j] == power(l@[j] as int, n as int),
        decreases l.len() - i,
    {
        let powered = compute_power(l[i], n);
        result.push(powered);
        
        assert(result.len() == i + 1);
        assert(result@[i as int] == powered);
        assert(powered == power(l@[i as int] as int, n as int));
        assert(forall|j: int| #![trigger result@[j]] 0 <= j < i + 1 ==> result@[j] == power(l@[j] as int, n as int));
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}