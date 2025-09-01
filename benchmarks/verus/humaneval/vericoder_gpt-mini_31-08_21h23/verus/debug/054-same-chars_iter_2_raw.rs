```vc-helpers
// no helpers needed
```

```vc-code
{
    let mut i: nat = 0;
    while i < s0.len()
        invariant i <= s0.len();
        invariant forall|k: nat| 0 <= k < i ==> s1@.contains(s0[k]);
        decreases s0.len() - i
    {
        if !s1@.contains(s0[i]) {
            return false;
        }
        i += 1;
    }

    let mut j: nat = 0;
    while j < s1.len()
        invariant j <= s1.len();
        invariant forall|k: nat| 0 <= k < j ==> s0@.contains(s1[k]);
        decreases s1.len() - j
    {
        if !s0@.contains(s1[j]) {
            return false;
        }
        j += 1;
    }

    proof {
        // prove forall i:int. 0 <= i < s0.len() ==> s1@.contains(s0[i])
        assert(forall|ii: int| 0 <= ii < s0.len() ==> s1@.contains(s0[ii]));
        proof {
            fix |ii: int|;
            assume H: 0 <= ii < s0.len();
            let k: nat = ii as nat;
            assert(k < s0.len());
            assert(s1@.contains(s0[k]));
            // indexing with an int index is definitionally the same as with the corresponding nat
            assert(s1@.contains(s0[ii]));
        }

        // prove forall i:int. 0 <= i < s1.len() ==> s0@.contains(s1[i])
        assert(forall|ii: int| 0 <= ii < s1.len() ==> s0@.contains(s1[ii]));
        proof {
            fix |ii: int|;
            assume H: 0 <= ii < s1.len();
            let k: nat = ii as nat;
            assert(k < s1.len());
            assert(s0@.contains(s1[k]));
            assert(s0@.contains(s1[ii]));
        }
    }

    true
}
```