// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool {
    n >= 2 && forall|k: int| #[trigger] (n % k) != 0 ==> (2 <= k < n ==> n % k != 0)
}

spec fn seq_product(factors: Seq<int>) -> int
    decreases factors.len()
{
    if factors.len() == 0 { 
        1 
    } else { 
        factors[0] * seq_product(factors.subrange(1, factors.len() as int))
    }
}

spec fn power(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 { 
        1 
    } else { 
        base * power(base, (exp - 1) as nat)
    }
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): runtime primality check with invariants and recorded divisor */
fn is_prime_check(n: i64) -> bool
    requires
        2 <= n && n < 100,
    ensures
        result == is_prime_number(n as int),
{
    let mut k: i64 = 2;
    let mut ok: bool = true;
    let mut d: i64 = 0;
    while k < n
        invariant
            2 <= k && k <= n,
            (ok ==> forall|k0: int| 2 <= k0 && k0 < k as int ==> (n as int) % k0 != 0),
            (!ok ==> (2 <= d && d < k && (n as int) % (d as int) == 0)),
        decreases ((n - k) as nat),
    {
        if n % k == 0 {
            ok = false;
            d = k;
            k = n;
        } else {
            k = k + 1;
        }
    }
    proof {
        if ok {
            assert(k == n);
            assert(forall|k0: int| 2 <= k0 && k0 < n as int ==> (n as int) % k0 != 0);
            assert(is_prime_number(n as int));
            assert(ok == is_prime_number(n as int));
        } else {
            assert(2 <= d);
            assert(d < n);
            assert((n as int) % (d as int) == 0);
            assert(exists|d0: int| 2 <= d0 && d0 < n as int && (n as int) % d0 == 0);
            assert(!is_prime_number(n as int));
            assert(ok == is_prime_number(n as int));
        }
    }
    ok
}

// </vc-helpers>

// <vc-spec>
fn is_multiply_prime(a: i8) -> (result: bool)
    requires 
        a >= 0 && a < 100
    ensures 
        a < 8 ==> result == false,
        result == true <==> (exists|p1: int, p2: int, p3: int|
            p1 >= 2 && p2 >= 2 && p3 >= 2 && 
            is_prime_number(p1) && is_prime_number(p2) && is_prime_number(p3) &&
            a as int == p1 * p2 * p3)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): iterate triples and use is_prime_check to decide result */
{
    let mut result: bool = false;
    let a_i64: i64 = a as i64;
    let mut i: i64 = 2;
    while i <= a_i64
        invariant
            2 <= i && i <= a_i64 + 1,
            result == (exists|p1: int, p2: int, p3: int|
                2 <= p1 && p1 < i as int &&
                2 <= p2 && p2 <= a as int &&
                2 <= p3 && p3 <= a as int &&
                is_prime_number(p1) && is_prime_number(p2) && is_prime_number(p3) &&
                a as int == p1 * p2 * p3),
        decreases ((a_i64 + 1) - i) as nat,
    {
        let mut j: i64 = 2;
        while !result && j <= a_i64
            invariant
                2 <= j && j <= a_i64 + 1,
                result == (exists|p1: int, p2: int, p3: int|
                    2 <= p1 && p1 == i as int &&
                    2 <= p2 && p2 < j as int &&
                    2 <= p3 && p3 <= a as int &&
                    is_prime_number(p1) && is_prime_number(p2) && is_prime_number(p3) &&
                    a as int == p1 * p2 * p3),
            decreases ((a_i64 + 1) - j) as nat,
        {
            let mut k: i64 = 2;
            while !result && k <= a_i64
                invariant
                    2 <= k && k <= a_i64 + 1,
                    result == (exists|p1: int, p2: int, p3: int|
                        2 <= p1 && p1 == i as int &&
                        2 <= p2 && p2 == j as int &&
                        2 <= p3 && p3 < k as int &&
                        is_prime_number(p1) && is_prime_number(p2) && is_prime_number(p3) &&
                        a as int == p1 * p2 * p3),
                decreases ((a_i64 + 1) - k) as nat,
            {
                if i * j * k == a_i64 {
                    if i >= 2 && j >= 2 && k >= 2 {
                        if i < 100 && j < 100 && k < 100 {
                            if is_prime_check(i) && is_prime_check(j) && is_prime_check(k) {
                                result = true;
                            }
                        }
                    }
                }
                k = k + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    if a < 8 {
        result = false;
    }
    result
}

// </vc-code>


}

fn main() {}