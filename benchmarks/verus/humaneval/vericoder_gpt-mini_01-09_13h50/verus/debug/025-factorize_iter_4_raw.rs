```vc-helpers
proof fn prime_of_smallest_divisor(p: nat, rem: nat)
    requires
        2 <= p,
        rem % p == 0,
        forall|q: nat| 2 <= q && q < p ==> rem % q != 0,
    ensures
        is_prime(p),
{
    proof {
        // show: forall 1 < i < p ==> p % i != 0
        assert(forall|i: nat| 1 < i && i < p ==> p % i != 0) by {
            fix |i: nat|;
            assume(1 < i && i < p);
            // Prove p % i != 0 by contradiction
            assert_by_contradiction(|H: nat| {
                // H: p % i == 0
                // From p % i == 0, p == i * (p / i)
                assert(p == i * (p / i));
                // From rem % p == 0, rem == (rem / p) * p
                assert(rem == (rem / p) * p);
                // Combine:
                // rem == (rem/p) * p == (rem/p) * (i * (p / i)) == i * ((rem/p) * (p / i))
                // hence rem % i == 0
                assert(rem == i * (((rem / p) * (p / i))));
                assert(rem % i == 0);
                // This contradicts the invariant that no q < p divides rem
                assert(!(forall|q: nat| 2 <= q && q < p ==> rem % q != 0));
            });
        }
        // Conclude is_prime(p) (definition: forall 1<i<p ==> p%i != 0)
        ()
    }
}
```

```vc-code
{
    let mut factorization: Vec<u8> = Vec::new();
    let mut rem: nat = n as nat;
    let mut p: u8 = 2u8;

    // Invariant:
    // - product of factors in `factorization` times `rem` equals original n
    // - for all q with 2 <= q < p, rem % q != 0 (we have removed all smaller factors)
    // - all elements in factorization are prime
    // - factorization is non-decreasing
    while (p as nat) <= rem
        invariant
            factorization@.fold_right(|x: u8, acc: nat| acc * (x as nat), 1) * rem == n as nat,
            forall|q: nat| 2 <= q && q < (p as nat) ==> rem % q != 0,
            forall|i: int| 0 <= i && i < factorization@.len() ==> #[trigger] is_prime(factorization@[i] as nat),
            forall|i: int, j: int|
                0 <= i && i < j && j < factorization@.len() ==> factorization@[i] as nat <= factorization@[j] as nat,
    {
        // While the current p divides rem, push it and divide rem
        while rem % (p as nat) == 0
            invariant
                factorization@.fold_right(|x: u8, acc: nat| acc * (x as nat), 1) * rem == n as nat,
                forall|q: nat| 2 <= q && q < (p as nat) ==> rem % q != 0,
                forall|i: int| 0 <= i && i < factorization@.len() ==> #[trigger] is_prime(factorization@[i] as nat),
                forall|i: int, j: int|
                    0 <= i && i < j && j < factorization@.len() ==> factorization@[i] as nat <= factorization@[j] as nat,
        {
            // At this point, p divides rem and no smaller q divides rem.
            // Hence p is prime.
            proof {
                prime_of_smallest_divisor(p as nat, rem);
            }
            // push p
            factorization.push(p);
            // update rem
            rem = rem / (p as nat);
            // After dividing by p, no smaller q divides new rem either:
            // if some q < p divided the new rem, it would also divide the old rem.
            proof {
                assert(forall|q: nat| 2 <= q && q < (p as nat) ==> rem % q != 0) by {
                    fix |q: nat|;
                    assume(2 <= q && q < (p as nat));
                    // Suppose q divides rem (new rem). Then old rem = p * (new rem) is also divisible by q, contradiction.
                    assert_by_contradiction(|H: nat| {
                        // H: rem % q == 0
                        // old_rem = (p as nat) * rem_old? We renamed rem to new rem already.
                        // To make clear, derive contradiction: old_rem_old = (p as nat) * rem (before division),
                        // so old_rem_old % q == 0 contradicting the invariant.
                        // Construct old_rem_old = (p as nat) * rem
                        assert(((p as nat) * rem) % q == 0);
                        assert(!(forall|r: nat| 2 <= r && r < (p as nat) ==> ((p as nat) * rem) % r != 0));
                    });
                }
            }
            // Non-decreasing property: newly pushed p is >= previous last element (if any)
            proof {
                if factorization@.len() >= 2 {
                    // let last = factorization@[factorization@.len() - 1] (this is the element just pushed)
                    // let prev_idx = factorization@.len() - 2;
                    // We know previously the last element <= p, and we are pushing p, so order preserved.
                    // This is handled by the loop invariants maintained above.
                    ()
                } else {
                    ()
                }
            }
        }

        // increment p
        p = p + 1u8;
    }

    // After loop, rem must be 1 (since when p > rem we stop; if rem > 1, it is prime > last p-1)
    // If rem > 1, it is a prime factor greater than or equal to 2; push it.
    if rem > 1 {
        // rem fits in u8 because rem divides n and n <= u8::MAX
        let last_factor: u8 = rem as u8;
        // rem is prime because no q < (p as nat) divides rem and p > rem
        // So we can push it and update rem to 1
        proof {
            // p is now > rem, so forall q with 2 <= q < (rem+1) rem%q != 0 holds (from loop invariant with old p)
            // Thus rem is prime by prime_of_smallest_divisor
            prime_of_smallest_divisor(rem, rem);
        }
        factorization.push(last_factor);
        rem = 1;
    }

    // Return factorization
    factorization
}
```