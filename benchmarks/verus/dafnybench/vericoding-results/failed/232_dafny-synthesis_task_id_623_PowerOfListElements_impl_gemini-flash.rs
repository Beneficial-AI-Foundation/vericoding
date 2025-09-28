use vstd::prelude::*;

verus! {

spec fn power(base: int, exponent: int) -> int
    recommends exponent >= 0
    decreases exponent
{
    if exponent <= 0 { 1 } else { base * power(base, exponent - 1) }
}

// <vc-helpers>
fn power_auto(base: int, exponent: int) -> int
    recommends exponent >= 0
    decreases exponent
{
    if exponent <= (0 as int) { (1 as int) } else { base * power_auto(base, (exponent - (1 as int)) as int) }
}

proof fn lemma_power_auto_eq_power(base: int, exponent: int)
    requires exponent >= 0
    ensures power_auto(base, exponent) == power(base, exponent)
    decreases exponent
{
    if exponent <= (0 as int) {
        assert(power_auto(base, exponent) == (1 as int));
        assert(power(base, exponent) == (1 as int));
    } else {
        lemma_power_auto_eq_power(base, (exponent - (1 as int)) as int);
        assert(power_auto(base, exponent) == base * power_auto(base, (exponent - (1 as int)) as int));
        assert(power(base, exponent) == base * power(base, (exponent - (1 as int)) as int));
    }
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
            i <= l.len(),
            result.len() == i,
            forall|k: int| 0 <= k && k < i as int ==> result@[k] == power(l[k as usize] as int, n as int),
    {
        let element = l[i];
        let ghost power_result_int = power(element as int, n as int); // Use ghost variable for int result
        result.push(power_result_int.into()); // Cast only at the end for the concrete type
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}