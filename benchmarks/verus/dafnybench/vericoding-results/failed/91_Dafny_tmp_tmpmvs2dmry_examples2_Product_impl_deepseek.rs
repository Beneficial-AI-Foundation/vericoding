use vstd::prelude::*;

verus! {

spec fn gcd(m: nat, n: nat) -> nat
recommends m > 0 && n > 0
decreases m + n
{
    if m == n { 
        n 
    } else if m > n { 
        gcd(sub(m, n), n)
    } else {
        gcd(m, sub(n, m))
    }
}

spec fn exp(x: real, n: nat) -> real
decreases n
{
    if n == 0 {
        1.0
    } else if x == 0.0 {
        0.0
    } else if n == 0 && x == 0.0 {
        1.0
    } else {
        x * exp(x, sub(n, 1))
    }
}

// <vc-helpers>
proof fn lemma_mul_commutes(x: nat, y: nat)
    ensures
        x * y == y * x,
{
}

proof fn lemma_mul_distributes_add(x: nat, y: nat, z: nat)
    ensures
        x * (y + z) == x * y + x * z,
{
}

proof fn lemma_mul_associates(x: nat, y: nat, z: nat)
    ensures
        x * (y * z) == (x * y) * z,
{
}

spec fn product_rec(m: nat, n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        m + product_rec(m, sub(n, 1))
    }
}

proof fn lemma_product_rec_equals_mul(m: nat, n: nat)
    ensures
        product_rec(m, n) == m * n,
    decreases n
{
    if n > 0 {
        lemma_product_rec_equals_mul(m, sub(n, 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn Product(m: u64, n: u64) -> (res: u64)
ensures res == m * n
// </vc-spec>
// <vc-code>
{
    let mut res: u64 = 0;
    let mut count: u64 = n;
    assert(m as nat * n as nat == product_rec(m as nat, n as nat)) by {
        lemma_product_rec_equals_mul(m as nat, n as nat);
    };
    while count > 0
        invariant
            count <= n,
            res as nat == product_rec(m as nat, (n - count) as nat),
    {
        res = res + m;
        count = count - 1;
        assert(res as nat == product_rec(m as nat, (n - count) as nat)) by {
            if count > 0 {
                lemma_product_rec_equals_mul(m as nat, (n - count) as nat);
            }
        };
    }
    assert(count == 0) by {
        assert(res as nat == product_rec(m as nat, n as nat));
        assert(product_rec(m as nat, n as nat) == m as nat * n as nat);
    };
    res
}
// </vc-code>

fn main() {}

}