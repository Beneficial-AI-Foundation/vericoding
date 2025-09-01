```vc-helpers
// (no helpers needed)
```

```vc-code
{
    // impl-start
    let mut j: nat = 1;
    let mut max: i32 = a[0];

    while j < a.len()
        invariant 0 < a.len();
        invariant j <= a.len();
        invariant forall|k: nat| k < j ==> a[k] <= max;
        invariant exists|k: nat| k < j && a[k] == max;
    {
        if a[j] > max {
            max = a[j];
        }
        j = j + 1;
    }

    proof {
        // From loop exit, j == a.len()
        assert(j == a.len());

        // From invariant, all elements in 0..j are <= max
        assert(forall|k: nat| k < j ==> a[k] <= max);

        // Convert the above to the required int-indexed form
        assert(forall|i: int| 0 <= i && i < a.len() ==> a[i as nat] <= max);
        proof {
            fix(i: int);
            assume(0 <= i && i < a.len());
            let k: nat = i as nat;
            assert(a[k] <= max);
        }

        // From invariant, some index k < j has a[k] == max
        assert(exists|k: nat| k < j && a[k] == max);

        // Choose such a k and produce an int-indexed witness
        let k: nat = choose(|k: nat| k < j && a[k] == max);
        let i: int = k as int;
        assert(0 <= i && i < a.len() && a[i as nat] == max);
    }

    max
    // impl-end
}
```