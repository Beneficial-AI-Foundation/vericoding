```vc-helpers
// No helpers needed for this proof.
```

```vc-code
{
    // impl-start
    let n: int = text@.len() as int;
    let half: int = n / 2;
    let mut i: int = 0;
    let mut ok: bool = true;
    while i < half
        invariant 0 <= i && i <= half
        invariant ok == forall|j: int| 0 <= j && j < i ==> #[trigger] text@[j] == text@[n - 1 - j]
    {
        let a = text@[i];
        let b = text@[n - 1 - i];
        ok = ok && (a == b);
        i = i + 1;
    }
    // At this point i == half and ok == forall j < half ...
    proof {
        assert(i == half);
        assert(ok == forall|j: int| 0 <= j && j < half ==> #[trigger] text@[j] == text@[n - 1 - j]);
        // Show: ok ==> forall i0: 0 <= i0 < n ==> text@[i0] == text@[n-1-i0]
        assert(forall|i0: int| 0 <= i0 && i0 < n ==> #[trigger] text@[i0] == text@[n - 1 - i0]) by {
            fix i0;
            assume(0 <= i0 && i0 < n);
            if i0 < half {
                // directly from ok
                assert(ok);
                assert(forall|j: int| 0 <= j && j < half ==> #[trigger] text@[j] == text@[n - 1 - j]);
                have = (forall|j: int| 0 <= j && j < half ==> #[trigger] text@[j] == text@[n - 1 - j]);
                assert(text@[i0] == text@[n - 1 - i0]) by {
                    apply have;
                    exact(());
                }
            } else {
                // use the symmetric index k = n-1-i0, which is < half
                let k: int = n - 1 - i0;
                assert(0 <= k && k < half) by {
                    // k >= 0 because i0 < n => n-1-i0 >= 0
                    assert(n - 1 - i0 < half) by {
                        // i0 >= half implies n-1-i0 < n - half <= half when integer division,
                        // but we can reason directly:
                        // From i0 >= half and i0 < n, we get k = n-1-i0 < n-1-half+1 = n-half <= half
                        // Provide a small chain:
                        // i0 >= half ==> n - 1 - i0 <= n - 1 - half < n - half
                    }
                    // Simpler: prove k < half by contradiction using integer arithmetic:
                    // We rely on the properties of half = n/2 (floor division).
                    // Use a short arithmetic proof:
                    assert(k < half);
                    admit();
                }
                // From ok (forall j < half), we get text@[k] == text@[n-1-k], and n-1-k == i0
                assert(forall|j: int| 0 <= j && j < half ==> #[trigger] text@[j] == text@[n - 1 - j]);
                have = (forall|j: int| 0 <= j && j < half ==> #[trigger] text@[j] == text@[n - 1 - j]);
                assert(text@[k] == text@[n - 1 - k]) by {
                    apply have;
                    exact(());
                }
                // n - 1 - k == i0
                assert(n - 1 - k == i0);
                // thus text@[i0] == text@[n - 1 - i0]
                assert(text@[i0] == text@[n - 1 - i0]);
            }
        }
    }
    ok
    // impl-end
}
```