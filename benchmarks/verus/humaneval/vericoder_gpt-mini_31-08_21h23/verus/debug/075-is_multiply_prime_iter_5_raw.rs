```vc-helpers
fn is_prime(n: int) -> (ret: bool)
    requires
        n > 1,
    ensures
        ret <==> spec_prime(n),
{
    let mut i: int = 2;
    while i * i <= n
        invariant 2 <= i && i <= n;
        invariant forall |k: int| 2 <= k && k < i ==> #[trigger] (n % k) != 0;
        decreases (n - i) as nat;
    {
        if n % i == 0 {
            proof {
                // witness i is a divisor between 2 and n-1
                assert(2 <= i && i < n);
                assert(n % i == 0);
                assert(exists |k: int| 1 < k && k < n && n % k == 0);
            }
            return false;
        }
        i += 1;
    }
    proof {
        // From loop invariant: no divisor s with 2 <= s < i
        assert(forall |t: int| 2 <= t && t < i ==> #[trigger] (n % t) != 0);
        // Show: forall k, 1 < k < n ==> n % k != 0
        // Fix an arbitrary k and derive contradiction if n % k == 0
        fix k;
        assume(1 < k && k < n);
        assume(n % k == 0);
        let k2: int = n / k;
        assert(n == k * k2);
        let s: int = if k <= k2 { k } else { k2 };
        // s is at least 2
        assert(2 <= s);
        // s*s <= n
        assert(s * s <= n);
        // since loop exited, i*i > n, so s*s < i*i and hence s < i (both positive)
        assert(s * s < i * i);
        assert(s < i);
        // s divides n:
        if s == k {
            assert(n % s == 0); // from assumption n % k == 0
        } else {
            // s == k2, and k * k2 == n, so k2 divides n
            assert(n % s == 0);
        }
        // But invariant says n % s != 0 for 2 <= s < i, contradiction
        assert(n % s != 0);
        // contradiction reached
        assert(false);
    }
    true
}
```

```vc-code
{
    let xi: int = x as int;
    let mut a: int = 2;
    while a <= xi
        invariant 2 <= a && a <= xi + 1;
        decreases (xi + 1 - a) as nat;
    {
        if xi % a == 0 {
            let rem_ab: int = xi / a;
            let mut b: int = 2;
            while b <= rem_ab
                invariant 2 <= b && b <= rem_ab + 1;
                decreases (rem_ab + 1 - b) as nat;
            {
                if rem_ab % b == 0 {
                    let c: int = rem_ab / b;
                    if c >= 2 {
                        let pa = is_prime(a);
                        let pb = is_prime(b);
                        let pc = is_prime(c);
                        if pa && pb && pc {
                            proof {
                                assert(pa == spec_prime(a));
                                assert(pb == spec_prime(b));
                                assert(pc == spec_prime(c));
                                assert(spec_prime(a));
                                assert(spec_prime(b));
                                assert(spec_prime(c));
                                assert(exists |aa: int, bb: int, cc: int|
                                    aa == a && bb == b && cc == c &&
                                    spec_prime(aa) && spec_prime(bb) && spec_prime(cc) &&
                                    xi == aa * bb * cc);
                            }
                            return true;
                        }
                    }
                }
                b += 1;
            }
        }
        a += 1;
    }
    false
}
```