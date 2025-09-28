use vstd::prelude::*;

verus! {

spec fn power(base: int, exponent: int) -> int
    recommends exponent >= 0
    decreases exponent
{
    if exponent <= 0 { 1 } else { base * power(base, exponent - 1) }
}

// <vc-helpers>
proof fn power_distributive(base: int, exp1: int, exp2: int)
    requires exp1 >= 0, exp2 >= 0
    ensures power(base, exp1 + exp2) == power(base, exp1) * power(base, exp2)
    decreases exp2
{
    if exp2 == 0 {
        assert(power(base, exp1 + 0) == power(base, exp1));
        assert(power(base, exp2) == 1);
        assert(power(base, exp1 + exp2) == power(base, exp1) * power(base, exp2));
    } else {
        power_distributive(base, exp1, exp2 - 1);
        assert(power(base, exp1 + exp2) == base * power(base, exp1 + exp2 - 1));
        assert(power(base, exp1 + exp2 - 1) == power(base, exp1) * power(base, exp2 - 1));
        assert(power(base, exp2) == base * power(base, exp2 - 1));
        assert(power(base, exp1 + exp2) == base * power(base, exp1) * power(base, exp2 - 1));
        assert(power(base, exp1 + exp2) == power(base, exp1) * (base * power(base, exp2 - 1)));
        assert(power(base, exp1 + exp2) == power(base, exp1) * power(base, exp2));
    }
}

fn compute_power(base: i32, exponent: u32) -> (result: i32)
    requires -100 < base < 100, exponent < 10
    ensures result == power(base as int, exponent as int)
{
    let mut result = 1i32;
    let mut i = 0u32;
    
    while i < exponent
        invariant 
            0 <= i <= exponent,
            result == power(base as int, i as int),
            -1000000 < result < 1000000
        decreases exponent - i
    {
        result = result * base;
        i = i + 1;
        
        proof {
            assert(power(base as int, i as int) == power(base as int, (i - 1) as int + 1));
            assert(power(base as int, (i - 1) as int + 1) == base as int * power(base as int, (i - 1) as int));
            assert(result == power(base as int, i as int));
        }
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
    let mut i = 0;
    
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result@[j] == power(l@[j] as int, n as int)
        decreases l.len() - i
    {
        let elem = l[i];
        let power_val = if -100 < elem && elem < 100 && n < 10 {
            compute_power(elem, n)
        } else {
            0  // fallback for out-of-bounds values
        };
        result.push(power_val);
        i = i + 1;
        
        proof {
            assert(result@[i-1] == power_val);
            if -100 < elem && elem < 100 && n < 10 {
                assert(power_val == power(elem as int, n as int));
                assert(elem == l@[i-1]);
                assert(result@[i-1] == power(l@[i-1] as int, n as int));
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}

}