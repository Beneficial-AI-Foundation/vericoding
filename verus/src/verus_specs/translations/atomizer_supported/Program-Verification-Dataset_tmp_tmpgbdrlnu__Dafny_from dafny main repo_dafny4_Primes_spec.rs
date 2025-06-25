use vstd::prelude::*;

verus! {

spec fn is_prime(n: int) -> bool {
    2 <= n && forall|m: int| 2 <= m < n ==> n % m != 0
}

proof fn always_more_primes(k: int)
    ensures exists|p: int| k <= p && is_prime(p)
{
    todo!()
}

proof fn no_finite_set_contains_all_primes(s: Set<int>)
    ensures exists|p: int| is_prime(p) && !s.contains(p)
{
    todo!()
}

spec fn all_primes(s: Set<int>, bound: int) -> bool {
    (forall|x: int| s.contains(x) ==> is_prime(x)) &&
    (forall|p: int| is_prime(p) && p <= bound ==> s.contains(p))
}

proof fn get_larger_prime(s: Set<int>, bound: int) -> (p: int)
    requires all_primes(s, bound)
    ensures bound < p && is_prime(p)
{
    todo!()
}

spec fn product(s: Set<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 1 } else {
        let a = pick_largest(s);
        a * product(s.remove(a))
    }
}

proof fn product_property(s: Set<int>)
    requires forall|x: int| s.contains(x) ==> 1 <= x
    ensures 1 <= product(s) && forall|x: int| s.contains(x) ==> x <= product(s)
{
    todo!()
}

proof fn product_plus_one_is_prime(s: Set<int>, q: int)
    requires all_primes(s, q) && q == product(s)
    ensures is_prime(q + 1)
{
    todo!()
}

proof fn remove_factor(x: int, s: Set<int>)
    requires s.contains(x)
    ensures product(s) == x * product(s.remove(x))
{
    todo!()
}

spec fn is_prime_alt(n: int) -> bool {
    2 <= n && forall|m: int| 2 <= m < n && is_prime(m) ==> n % m != 0
}

proof fn alt_prime_definition(n: int)
    requires is_prime_alt(n)
    ensures is_prime(n)
{
    todo!()
}

proof fn composite(c: int) -> (a: int, b: int)
    requires 2 <= c && !is_prime(c)
    ensures 2 <= a < c && 2 <= b && a * b == c
    ensures is_prime(a)
{
    todo!()
}

spec fn pick_largest(s: Set<int>) -> int
    requires s.len() != 0
{
    arbitrary()
}

proof fn largest_element_exists(s: Set<int>)
    requires s.len() != 0
    ensures exists|x: int| s.contains(x) && forall|y: int| s.contains(y) ==> y <= x
{
    todo!()
}

proof fn mul_pos(a: int, b: int)
    requires 1 <= a && 1 <= b
    ensures a <= a * b
{
    todo!()
}

proof fn mul_div_mod(a: nat, b: nat, c: nat, j: nat)
    requires a * b == c && j < a
    ensures (c + j) % a == j
{
    todo!()
}

}