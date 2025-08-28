use vstd::prelude::*;

verus! {

spec fn power(base: int, exponent: int) -> int
    recommends exponent >= 0
    decreases exponent
{
    if exponent <= 0 { 1 } else { base * power(base, exponent - 1) }
}

// <vc-helpers>
proof fn lemma_power_positive(base: int, exponent: int)
    requires
        exponent >= 0,
    ensures
        power(base, exponent) >= 1 || base == 0,
    decreases exponent
{
    if exponent > 0 {
        lemma_power_positive(base, exponent - 1);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn power_of_list_elements(l: Vec<i32>, n: u32) -> (result: Vec<i32>)
    ensures 
        result.len() == l.len(),
        forall|i: int| #![auto] 0 <= i < l.len() ==> result[i] == power(l[i] as int, n as int),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn power_of_list_elements(l: Vec<i32>, n: u32) -> (result: Vec<i32>)
    ensures
        result.len() == l.len(),
        forall|i: int| #![auto] 0 <= i < l.len() ==> result[i] == power(l[i] as int, n as int),
{
    let mut res: Vec<i32> = Vec::with_capacity(l.len());
    let mut i: usize = 0;
    while i < l.len()
        invariant
            res.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> res[j] == power(l[j] as int, n as int),
    {
        let mut val: int = 1;
        let mut exp: int = n as int;
        let base: int = l[i] as int;
        while exp > 0
            invariant
                exp >= 0,
                val == power(base, n as int - exp),
            decreases exp
        {
            val = val * base;
            exp = exp - 1;
        }
        res.push(val as i32);
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {}

}