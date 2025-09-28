use vstd::prelude::*;

verus! {

spec fn power(base: int, exponent: int) -> int
    recommends exponent >= 0
    decreases exponent
{
    if exponent <= 0 { 1 } else { base * power(base, exponent - 1) }
}

// <vc-helpers>
fn pow(base: i32, exp: u32) -> (res: i32)
    requires power(base as int, exp as int) <= 0x7fffffff_i32 as int,
             power(base as int, exp as int) >= -0x80000000_i32 as int
    ensures res as int == power(base as int, exp as int)
    decreases exp as int
{
    if exp == 0 {
        1
    } else {
        let prev = pow(base, exp - 1);
        base * prev
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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < l.len()
        invariant 
            i <= l.len(),
            result.len() == i,
            forall|j: usize| #[trigger] 0 <= j < i ==> result@[j as int] == power(l@[j as int] as int, n as int)
    {
        proof {
            assert(power(l@[i as int] as int, n as int) <= 0x7fffffff_i32 as int);
            assert(power(l@[i as int] as int, n as int) >= -0x80000000_i32 as int);
        }
        let val = pow(l[i], n);
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}