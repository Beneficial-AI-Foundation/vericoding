```vc-helpers
proof fn extend_nondivisors(n: int, i: int)
    requires 2 <= i && i < n;
    requires forall|k: int| 2 <= k && k < i ==> n % k != 0;
    requires n % i != 0;
    ensures forall|k: int| 2 <= k && k < i + 1 ==> n % k != 0
{
    assert(forall|k: int| 2 <= k && k < i + 1 ==> n % k != 0 by {
        let k: int;
        assume Hk: 2 <= k && k < i + 1;
        if k < i {
            // then k satisfies 2 <= k < i, so use the forall precondition
            assert(n % k != 0);
        } else {
            // k >= i and k < i+1 implies k == i
            assert(k == i);
            assert(n % i != 0);
        }
    });
}
```

```vc-code
{
    let n = str.len();
    if n < 2 {
        return false;
    }
    let mut i: usize = 2;
    while i < n
        invariant (2 as int) <= (i as int) && (i as int) <= (n as int);
        invariant forall|k: int| 2 <= k && k < (i as int) ==> ((n as int) % k != 0);
        decreases n - i;
    {
        if n % i == 0 {
            return false;
        }
        // use a proof lemma to extend the forall invariant to i+1
        proof {
            extend_nondivisors(n as int, i as int);
        }
        i += 1;
    }
    true
}
```