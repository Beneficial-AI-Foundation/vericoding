```vc-helpers
// no helpers needed
```

```vc-code
{
    let n = a.len();
    assert(n > 0);
    let mut i: usize = 1;
    let mut ans: usize = 0;
    while i < n
        invariant ans < n;
        invariant i <= n;
        invariant forall |k: int| 0 <= k && k < (i as int) ==> #[trigger] a[k] <= a[ans as int];
        decreases n - i;
    {
        let old_ans = ans;
        if a[i as int] > a[old_ans as int] {
            // prove for all k < i: a[k] <= a[i]
            assert(forall |k: int| 0 <= k && k < (i as int) ==> #[trigger] a[k] <= a[i as int]) by {
                fix k;
                assume Hk: 0 <= k && k < (i as int);
                // from the loop invariant before update: a[k] <= a[old_ans]
                assert(a[k] <= a[old_ans as int]);
                // from the if condition: a[old_ans] < a[i]
                assert(a[old_ans as int] < a[i as int]);
                // combine to get a[k] <= a[i]
                assert(a[k] < a[i as int]);
                assert(a[k] <= a[i as int]);
            };
            ans = i;
        } else {
            // ans unchanged
        }

        // prove a[i] <= a[ans] after the if (case analysis)
        if a[i as int] > a[old_ans as int] {
            // then ans == i
            assert(a[i as int] <= a[ans as int]);
        } else {
            // then a[i] <= old_ans == ans
            assert(a[i as int] <= a[ans as int]);
        }

        // prove the invariant for i+1: forall k < i+1, a[k] <= a[ans]
        assert(forall |k: int| 0 <= k && k < ((i + 1) as int) ==> #[trigger] a[k] <= a[ans as int]) by {
            fix k;
            assume Hk: 0 <= k && k < ((i + 1) as int);
            if k < (i as int) {
                // two cases depending on whether ans was updated
                if a[i as int] > a[old_ans as int] {
                    // we proved forall k < i: a[k] <= a[i], and ans == i
                    assert(a[k] <= a[i as int]);
                    assert(a[k] <= a[ans as int]);
                } else {
                    // ans unchanged, original invariant gives a[k] <= a[ans]
                    assert(a[k] <= a[ans as int]);
                }
            } else {
                // k == i
                assert(a[k] <= a[ans as int]);
            }
        };

        i = i + 1;
    }
    ans
}
```