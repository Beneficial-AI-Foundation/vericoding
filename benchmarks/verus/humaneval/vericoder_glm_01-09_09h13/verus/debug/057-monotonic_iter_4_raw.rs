```vc-helpers
proof fn monotonic_lemma(l: Vec<i32>, i: int, j: int, b: bool)
    requires
        0 <= i < j < l@.len(),
        b <==> (forall|k: int, m: int| 0 <= k < m < l@.len() ==> l@[k] <= l@[m]),
    ensures
        b ==> l@[i] <= l@[j]
{
    if b {
        assert(l@[i] <= l@[j]);
    }
}

proof fn antimonotonic_lemma(l: Vec<i32>, i: int, j: int, b: bool)
    requires
        0 <= i < j < l@.len(),
        b <==> (forall|k: int, m: int| 0 <= k < m < l@.len() ==> l@[k] >= l@[m]),
    ensures
        b ==> l@[i] >= l@[j]
{
    if b {
        assert(l@[i] >= l@[j]);
    }
}

proof fn propagate_monotonic(l: Vec<i32>, i: int, increasing: bool, decreasing: bool)
    requires
        0 <= i < l@.len() - 1,
        increasing <==> (forall|k: int, m: int| 0 <= k < m <= i ==> l@[k] <= l@[m]),
        decreasing <==> (forall|k: int, m: int| 0 <= k < m <= i ==> l@[k] >= l@[m]),
    ensures
        (l[i] <= l[i + 1] ==> increasing) && (l[i] >= l[i + 1] ==> decreasing),
{
    if l[i] <= l[i + 1] {
        if decreasing {
            assert(forall|k: int, m: int| 0 <= k < m <= i ==> l@[k] >= l@[m]);
            assert(forall|k: int, m: int| 0 <= k < m <= i + 1 ==> l@[k] >= l@[m]) by {
                let k, m: int;
                assume(0 <= k < m <= i + 1);
                if m <= i {
                    assert(l@[k] >= l@[m]);
                } else {
                    assert(l@[k] >= l@[m]);
                }
            };
        }
    }
    if l[i] >= l[i + 1] {
        if increasing {
            assert(forall|k: int, m: int| 0 <= k < m <= i ==> l@[k] <= l@[m]);
            assert(forall|k: int, m: int| 0 <= k < m <= i + 1 ==> l@[k] <= l@[m]) by {
                let k, m: int;
                assume(0 <= k < m <= i + 1);
                if m <= i {
                    assert(l@[k] <= l@[m]);
                } else {
                    assert(l@[k] <= l@[m]);
                }
            };
        }
    }
}
```

```vc-code
{
    let n = l.len();
    if n <= 1 {
        true
    } else {
        let mut increasing = true;
        let mut decreasing = true;
        let mut i = 0;
        
        while i < n - 1
            invariant
                0 <= i < n,
                increasing <==> (forall|k: int, m: int| 0 <= k < m <= i ==> l@[k] <= l@[m]),
                decreasing <==> (forall|k: int, m: int| 0 <= k < m <= i ==> l@[k] >= l@[m]),
            decreases n - 1 - i,
        {
            propagate_monotonic(l, i, increasing, decreasing);
            
            if l[i] > l[i + 1] {
                increasing = false;
            }
            if l[i] < l[i + 1] {
                decreasing = false;
            }
            
            proof {
                if increasing {
                    assert(forall|k: int, m: int| 0 <= k < m <= i + 1 ==> l@[k] <= l@[m]) by {
                        let k, m: int;
                        assume(0 <= k < m <= i + 1);
                        if m <= i {
                            assert(l@[k] <= l@[m]);
                        } else {
                            if k <= i {
                                assert(l@[k] <= l@[m]);
                            }
                        }
                    };
                }
                if decreasing {
                    assert(forall|k: int, m: int| 0 <= k < m <= i + 1 ==> l@[k] >= l@[m]) by {
                        let k, m: int;
                        assume(0 <= k < m <= i + 1);
                        if m <= i {
                            assert(l@[k]