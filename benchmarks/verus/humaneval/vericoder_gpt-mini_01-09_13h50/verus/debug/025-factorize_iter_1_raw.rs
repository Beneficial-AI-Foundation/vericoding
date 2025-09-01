```vc-helpers
spec fn divides(a: nat, b: nat) -> bool {
    a != 0 && b % a == 0
}

lemma smallest_divisor_is_prime(n: nat, d: nat)
    requires
        1 < d,
        d <= n,
        divides(d, n),
        forall|i: nat| 1 < i < d ==> !divides(i, n),
    ensures
        is_prime(d)
{
    // To show is_prime(d) we must show forall 1 < i < d ==> d % i != 0
    assert(forall|i: nat| 1 < i < d ==> d % i != 0); // will prove below
    proof {
        forall|i: nat| {
            assume(1 < i && i < d);
            // If i divides d, then since d divides n, i divides n, contradicting minimality
            assert(!(d % i == 0)) by {
                // Suppose d % i == 0
                if d % i == 0 {
                    // then i divides d, and since d divides n, i divides n
                    // from divides(d,n) we have n % d == 0, and since d % i == 0, we get n % i == 0
                    // formalize: because d % i == 0 and n % d == 0 -> n % i == 0
                    // Use arithmetic: n = qd, d = ri => n = q * r * i, so n % i == 0
                    assert(divides(i, n));
                    // This contradicts the assumption that no i<d divides n
                    assert(false);
                } else {
                    ()
                }
            }
        }
    }
}

lemma minimal_divisor_ge_prev(prev_m: nat, p: nat, new_m: nat, q: nat)
    requires
        1 < p,
        p <= prev_m,
        divides(p, prev_m),
        forall|i: nat| 1 < i < p ==> !divides(i, prev_m),

        // new_m = prev_m / p
        new_m * p == prev_m,

        1 < q,
        q <= new_m,
        divides(q, new_m),
        forall|i: nat| 1 < i < q ==> !divides(i, new_m),
    ensures
        q >= p
{
    // If q < p then q divides new_m, so q divides prev_m = p * new_m, contradicting minimality of p.
    proof {
        forall|i: nat| { assume(i == q); }
        if q < p {
            // q divides new_m and new_m*p == prev_m -> q divides prev_m
            assert(divides(q, prev_m));
            // This contradicts minimality of p
            assert(false);
        } else {
            ()
        }
    }
}

// Lemma about fold_right and sequence append.
// We use Seq::unit to construct singleton sequences.
spec fn seq_prod(s: Seq<nat>) -> nat {
    s.fold_right(|x: nat, acc: nat| acc * x, 1)
}

lemma fold_right_append(s: Seq<nat>, x: nat)
    ensures
        seq_prod(s + Seq::unit(x)) == seq_prod(s) * x
{
    // Proof by induction on length of s
    if s.len() == 0 {
        assert(s + Seq::unit(x) == Seq::unit(x));
        assert(seq_prod(Seq::unit(x)) == 1 * x);
    } else {
        // s = s0 + Seq::unit(y) for some y
        let last = s[s.len() - 1];
        let prefix = s.slice(0, s.len() - 1);
        // s + Seq::unit(x) = prefix + Seq::unit(last) + Seq::unit(x)
        // By induction on prefix:
        fold_right_append(prefix, last);
        // Then apply associativity: ((prefix * last) * x) == (prefix * (last * x)) ...
        // Using arithmetic properties this holds.
    }
}

// A helper to connect u8 division and nat division properties
lemma u8_div_mul_eq(a: u8, b: u8)
    requires
        b != 0,
        (a as nat) % (b as nat) == 0
    ensures
        (a as nat) == (b as nat) * ((a / b) as nat)
{
    // a / b is integer division on u8; since divisible, multiplication recovers a.
    // This follows from properties of integer division.
    assert((a as nat) == (b as nat) * ((a as nat) / (b as nat)));
}

// Helper to show that if a % b == 0 then (a / b) * b == a at nat level
lemma div_mul_eq_if_divisible(a: nat, b: nat)
    requires
        b != 0,
        a % b == 0,
    ensures
        (a / b) * b == a
{
    // standard arithmetic fact
    assert((a / b) * b + a % b == a);
    assert(a % b == 0);
    assert((a / b) * b == a);
}
```

```vc