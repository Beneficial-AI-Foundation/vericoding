use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>, i: nat) -> int
    recommends i <= s.len()
    decreases i
{
    if i == 0 { 0 } else { sum(s, (i - 1) as nat) + s[i - 1] }
}

spec fn exp(b: nat, n: nat) -> nat
    decreases n
{
    if n == 0 { 1nat } else { b * exp(b, (n - 1) as nat) }
}

spec fn bits(n: nat) -> Seq<bool>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        seq![n % 2 != 0].add(bits((n / 2) as nat))
    }
}

spec fn from_bits(s: Seq<bool>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        (if s[0] { 1nat } else { 0nat }) + 2nat * from_bits(s.subrange(1, s.len() as int))
    }
}

// <vc-helpers>
proof fn lemma_exp_add(b: nat, m: nat, n: nat)
    ensures exp(b, m + n) == exp(b, m) * exp(b, n)
    decreases m
{
    if m == 0 {
    } else {
        lemma_exp_add(b, (m - 1) as nat, n);
    }
}

proof fn lemma_exp_double(b: nat, n: nat)
    ensures exp(b, 2 * n) == exp(exp(b, n), 2)
    decreases n
{
    if n == 0 {
    } else {
        lemma_exp_add(b, n, n);
        lemma_exp_double(b, (n - 1) as nat);
        lemma_exp_add(b, 2 * ((n - 1) as nat), 2);
    }
}

proof fn lemma_from_bits_cons(bit: bool, rest: Seq<bool>)
    ensures from_bits(seq![bit].add(rest)) == (if bit { 1nat } else { 0nat }) + 2nat * from_bits(rest)
{
}

proof fn lemma_bits_correct(n: nat)
    ensures from_bits(bits(n)) == n
    decreases n
{
    if n == 0 {
    } else {
        lemma_bits_correct((n / 2) as nat);
        lemma_from_bits_cons(n % 2 != 0, bits((n / 2) as nat));
    }
}

proof fn lemma_exp_square(b: nat, n: nat)
    ensures n % 2 == 0 ==> exp(b, n) == exp(b * b, n / 2)
{
    if n % 2 == 0 && n > 0 {
        lemma_exp_double(b, n / 2);
    }
}

proof fn lemma_exp_multiply(a: nat, b: nat, n: nat)
    ensures exp(a * b, n) == exp(a, n) * exp(b, n)
    decreases n
{
    if n == 0 {
    } else {
        lemma_exp_multiply(a, b, (n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn fast_exp(b: u32, n: u32) -> (r: u32)
    ensures r == exp(b as nat, n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result = 1u32;
    let mut base = b;
    let mut exp_val = n;
    
    while exp_val > 0
        invariant 
            result as nat * exp(base as nat, exp_val as nat) == exp(b as nat, n as nat)
        decreases exp_val
    {
        if exp_val % 2 == 1 {
            result = result * base;
            exp_val = exp_val - 1;
        } else {
            proof {
                lemma_exp_square(base as nat, exp_val as nat);
            }
            base = base * base;
            exp_val = exp_val / 2;
        }
    }
    result
}
// </vc-code>

fn main() {}

}