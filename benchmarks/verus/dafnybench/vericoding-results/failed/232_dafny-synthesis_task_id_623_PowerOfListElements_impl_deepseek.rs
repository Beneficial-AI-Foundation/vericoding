use vstd::prelude::*;

verus! {

spec fn power(base: int, exponent: int) -> int
    recommends exponent >= 0
    decreases exponent
{
    if exponent <= 0 { 1 } else { base * power(base, exponent - 1) }
}

// <vc-helpers>
proof fn lemma_power_nonnegative(base: int, exponent: int)
    requires
        exponent >= 0,
    ensures
        power(base, exponent) >= 0 || base < 0,
    decreases exponent
{
    if exponent > 0 {
        lemma_power_nonnegative(base, exponent - 1);
    }
}

proof fn lemma_power_zero(exponent: int)
    requires
        exponent >= 0,
    ensures
        power(0, exponent) == 0 || exponent == 0,
    decreases exponent
{
    if exponent > 0 {
        lemma_power_zero(exponent - 1);
    }
}

proof fn lemma_power_one(exponent: int)
    requires
        exponent >= 0,
    ensures
        power(1, exponent) == 1,
    decreases exponent
{
    if exponent > 0 {
        lemma_power_one(exponent - 1);
    }
}

spec fn vec_to_seq(v: Vec<i32>) -> Seq<int>
    recommends v.len() >= 0
{
    Seq::new(v.len() as nat, |i: int| v@[i] as int)
}

proof fn lemma_power_positive(base: int, exponent: int)
    requires
        exponent >= 0,
        base >= 0,
    ensures
        power(base, exponent) >= 0,
    decreases exponent
{
    if exponent > 0 {
        lemma_power_positive(base, exponent - 1);
    }
}

proof fn lemma_power_multiplicative(base: int, exponent: int, remaining: int)
    requires
        exponent >= 0,
        remaining >= 0,
        exponent + remaining >= 0,
    ensures
        power(base, exponent + remaining) == power(base, exponent) * power(base, remaining),
    decreases exponent
{
    if exponent <= 0 {
        assert(power(base, 0 + remaining) == 1 * power(base, remaining));
    } else {
        lemma_power_multiplicative(base, exponent - 1, remaining);
        assert(power(base, exponent + remaining) == base * power(base, exponent - 1 + remaining));
        assert(power(base, exponent) * power(base, remaining) == base * power(base, exponent - 1) * power(base, remaining));
    }
}

proof fn lemma_power_definition(base: int, exponent: nat)
    ensures
        exponent > 0 ==> power(base, exponent) == base * power(base, exponent - 1)
{
    if exponent > 0 {
        assert(power(base, exponent) == base * power(base, exponent - 1)) by (compute);
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
    let mut result = Vec::with_capacity(l.len());
    let mut index: usize = 0;
    let ghost n_int = n as int;
    
    while index < l.len()
        invariant
            0 <= index <= l.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result@[i] == power(l@[i] as int, n_int),
        decreases l.len() - index
    {
        let element = l[index];
        let mut exp: u32 = n;
        let mut current: i32 = 1;
        
        proof {
            let base_int = element as int;
            if n_int >= 0 {
                lemma_power_nonnegative(base_int, n_int);
            }
        }
        
        while exp > 0
            invariant
                exp <= n,
                current as int == power(element as int, (n - exp) as int),
            decreases exp
        {
            let ghost base_int = element as int;
            let ghost prev_exp = (n - exp) as int;
            let ghost next_exp = (n - exp + 1) as int;
            
            proof {
                lemma_power_definition(base_int, next_exp as nat);
                assert(power(base_int, next_exp) == base_int * power(base_int, prev_exp));
            }
            
            current *= element;
            exp -= 1;
            
            proof {
                assert((n - exp) as int == next_exp);
                assert(current as int == (element as int) * power(element as int, prev_exp));
                assert(current as int == power(element as int, next_exp));
            }
        }
        
        result.push(current);
        index += 1;
        
        proof {
            assert(result@[index - 1] == current);
            assert(current as int == power(element as int, n_int));
            assert(l@[index - 1] == element);
        }
    }
    
    result
}
// </vc-code>

fn main() {}

}