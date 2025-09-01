```vc-helpers
// No helper functions needed for this proof.
```

```vc-code
{
    let seq: Seq<char> = s@;
    if seq.len() < 3 {
        return false;
    }
    let mut i: int = 1;
    while i + 1 < seq.len()
        invariant 0 < i && i + 1 <= seq.len();
        invariant forall|j: int| 0 < j && j + 1 < seq.len() && j < i ==> three_distinct_spec(seq, j);
        decreases seq.len() - i;
    {
        let a = seq@[i - 1];
        let b = seq@[i];
        let c = seq@[i + 1];
        if !(a != b && b != c) {
            return false;
        }
        proof {
            // Show the triple at index i satisfies the spec
            assert(seq@[i - 1] == a);
            assert(seq@[i] == b);
            assert(seq@[i + 1] == c);
            assert(a != b);
            assert(b != c);
            assert(seq@[i - 1] != seq@[i]);
            assert(seq@[i] != seq@[i + 1]);
            assert(seq@[i] != seq@[i + 1]);
            assert(three_distinct_spec(seq, i));

            // Prove the strengthened forall for the next iteration: j < i+1
            // by case analysis on j
            assert(forall|j: int| 0 < j && j + 1 < seq.len() && j < i + 1 ==>
                three_distinct_spec(seq, j));
            {
                fix j;
                assume H: 0 < j && j + 1 < seq.len() && j < i + 1;
                if j < i {
                    // this case follows from the current loop invariant
                    assert(three_distinct_spec(seq, j));
                } else {
                    // j >= i and j < i+1 implies j == i, so use the triple we just proved
                    assert(i <= j);
                    assert(j <= i);
                    assert(i == j);
                    assert(three_distinct_spec(seq, j));
                }
            }
        }
        i = i + 1;
    }
    return true;
}
```