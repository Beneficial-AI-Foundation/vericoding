use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_div_mod(x: int, d: int)
    requires
        d != 0,
    ensures
        x == d * (x / d) + (x % d),
        (x % d) >= 0,
        (x % d) < d,
{
    vstd::arithmetic::div_mod::lemma_div_mod(x, d);
}

proof fn lemma_div_mod_range(x: int, d: int)
    requires
        100 <= x < 1000,
        d == 10 || d == 100,
    ensures
        (x / d) >= 0,
        (x / d) < 10,
        (x % d) >= 0,
        (x % d) < d,
{
    lemma_div_mod(x, d);
    if d == 10 {
        assert(x / d < 10) by { vstd::arithmetic::div_mod::lemma_small_div(x, d); };
    } else {
        assert(x / d < 10) by { vstd::arithmetic::div_mod::lemma_small_div(x, d); };
    }
}

proof fn lemma_three_digit_decomposition(n: int)
    requires
        100 <= n < 1000,
    ensures
        n == (n / 100) * 100 + (n % 100),
        (n % 100) == ((n / 10) % 10) * 10 + (n % 10),
        (n / 100) >= 1 && (n / 100) < 10,
        ((n / 10) % 10) >= 0 && ((n / 10) % 10) < 10,
        (n % 10) >= 0 && (n % 10) < 10,
{
    lemma_div_mod_range(n, 100);
    lemma_div_mod_range(n, 10);
    lemma_div_mod_range(n / 10, 10);
    
    assert((n / 10) % 10 == (n / 10) - 10 * (n / 100)) by {
        lemma_div_mod(n / 10, 10);
    };
    
    assert(n % 100 == (n / 10) % 10 * 10 + n % 10) by {
        lemma_div_mod(n, 100);
        lemma_div_mod(n % 100, 10);
    };
}
// </vc-helpers>

// <vc-spec>
fn is_armstrong(n: int) -> (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
// </vc-spec>
// <vc-code>
{
    let hundreds = n / 100;
    let tens = (n / 10) % 10;
    let units = n % 10;
    
    proof {
        lemma_three_digit_decomposition(n);
        assert(n == hundreds * 100 + tens * 10 + units);
    }
    
    let sum_cubes = hundreds * hundreds * hundreds + tens * tens * tens + units * units * units;
    
    let result = n == sum_cubes;
    
    proof {
        assert(result <==> (n == hundreds * hundreds * hundreds + tens * tens * tens + units * units * units));
    }
    
    result
}
// </vc-code>

fn main() {
}

}