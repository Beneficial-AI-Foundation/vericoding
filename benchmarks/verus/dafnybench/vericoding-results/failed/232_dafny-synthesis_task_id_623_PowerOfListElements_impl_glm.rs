use vstd::prelude::*;

verus! {

spec fn power(base: int, exponent: int) -> int
    recommends exponent >= 0
    decreases exponent
{
    if exponent <= 0 { 1 } else { base * power(base, exponent - 1) }
}

// <vc-helpers>
fn exec_power(base: i32, exponent: u32) -> (result: i32)
    ensures result == power(base as int, exponent as int)
{
    let mut result = 1;
    let mut exp = exponent;
    while exp > 0
        invariant 
            exp <= exponent,
            result * power(base as int, exp as int) == power(base as int, exponent as int)
        decreases exp
    {
        result = result * base;
        exp = exp - 1;
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
    let mut result = Vec::new();
    for i in 0..l.len()
        invariant 
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == power(l@[j] as int, n as int)
    {
        let p = exec_power(l[i], n);
        result.push(p);
    }
    result
}
// </vc-code>

fn main() {}

}