```vc-helpers
// (no helpers needed)
```

```vc-code
{
    let n = str.len();
    if n < 2 {
        return false;
    }
    let mut i: usize = 2;
    while i < n
        invariant ((2 as int) <= (i as int) && (i as int) <= (n as int));
        invariant (forall|k: int| 2 <= k && k < (i as int) ==> ((n as int) % k != 0));
        decreases (n as int) - (i as int);
    {
        if n % i == 0 {
            return false;
        }
        // we know n % i != 0 for current i
        assert((n as int) % (i as int) != 0);
        // prove the forall invariant for i+1
        proof {
            assert(forall|k: int| 2 <= k && k < ((i as int) + 1) ==> ((n as int) % k != 0));
            {
                fix k: int;
                assume (2 <= k && k < ((i as int) + 1));
                if k < (i as int) {
                    // use the current forall invariant for k < i
                    assert((n as int) % k != 0);
                } else {
                    // k == i
                    assert(k == (i as int));
                    assert((n as int) % k != 0);
                }
            }
        }
        i += 1;
    }
    true
}
```