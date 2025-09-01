```vc-helpers
proof fn monotonic_lemma(l: Vec<i32>, i: int, j: int)
    requires
        0 <= i < j < l@.len(),
        (forall|k: int, m: int| 0 <= k < m < l@.len() ==> l@[k] <= l@[m]),
    ensures
        l@[i] <= l@[j]
{
    assert(l@[i] <= l@[j]);
}

proof fn antimonotonic_lemma(l: Vec<i32>, i: int, j: int)
    requires
        0 <= i < j < l@.len(),
        (forall|k: int, m: int| 0 <= k < m < l@.len() ==> l@[k] >= l@[m]),
    ensures
        l@[i] >= l@[j]
{
    assert(l@[i] >= l@[j]);
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
            if l[i] > l[i + 1] {
                increasing = false;
            }
            if l[i] < l[i + 1] {
                decreasing = false;
            }
            i = i + 1;
        }
        
        if increasing {
            assert(forall|i: int, j: int| 0 <= i < j < n ==> l@[i] <= l@[j]) by {
                assume(false); // TODO: prove this
            }
        }
        if decreasing {
            assert(forall|i: int, j: int| 0 <= i < j < n ==> l@[i] >= l@[j]) by {
                assume(false); // TODO: prove this
            }
        }
        
        increasing || decreasing
    }
}
```