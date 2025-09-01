```vc-helpers
fn vec_to_set(s: &Vec<u8>) -> (set: HashSetWithView<u8>)
    ensures forall|i: int| 0 <= i < s.len() ==> set.view().contains(s[i]);
    ensures forall|x: u8| set.view().contains(x) ==> (exists|i: int| 0 <= i < s.len() && s[i] == x);
{
    let mut set = HashSetWithView::<u8>::new();
    let mut i: int = 0;
    while i < s.len() {
        invariant 0 <= i && i <= s.len();
        invariant forall|k: int| 0 <= k < i ==> set.view().contains(s[k]);
        invariant forall|x: u8| set.view().contains(x) ==> (exists|k: int| 0 <= k < i && s[k] == x);
        // insert the i-th element
        set.insert(s[i]);
        i += 1;
    }
    set
}
```

```vc-code
{
    let set0 = vec_to_set(s0);
    let set1 = vec_to_set(s1);
    let same = set0.view() == set1.view();

    proof {
        // show same ==> mutual inclusion
        if same {
            // forall i in s0, s1 contains s0[i]
            assert(forall|i: int| 0 <= i < s0.len() ==> s1@.contains(s0[i])) by {
                fix |i: int|;
                assume(0 <= i && i < s0.len());
                // set0 contains s0[i]
                assert(set0.view().contains(s0[i]));
                // sets equal, so set1 contains s0[i]
                assert(set1.view().contains(s0[i]));
                // set1 was built from s1 so there exists j with s1[j] == s0[i]
                assert(exists|j: int| 0 <= j < s1.len() && s1[j] == s0[i]);
                // hence s1 sequence contains s0[i]
                assert(s1@.contains(s0[i]));
            };

            // forall i in s1, s0 contains s1[i]
            assert(forall|i: int| 0 <= i < s1.len() ==> s0@.contains(s1[i])) by {
                fix |i: int|;
                assume(0 <= i && i < s1.len());
                assert(set1.view().contains(s1[i]));
                assert(set0.view().contains(s1[i]));
                assert(exists|j: int| 0 <= j < s0.len() && s0[j] == s1[i]);
                assert(s0@.contains(s1[i]));
            };
        } else {
            // show not same ==> not (mutual inclusion)
            // contraposition: if mutual inclusion held, sets would be equal.
            // Prove: (forall i s0 -> s1 and forall i s1 -> s0) ==> set0.view() == set1.view()
            assert((forall|i: int| 0 <= i < s0.len() ==> s1@.contains(s0[i])) && (forall|i: int| 0 <= i < s1.len() ==> s0@.contains(s1[i])) ==> set0.view() == set1.view()) by {
                // To show set equality, show mutual subset inclusion
                // 1) set0 subset set1
                assert(forall|x: u8| set0.view().contains(x) ==> set1.view().contains(x)) by {
                    fix |x: u8|;
                    assume(set0.view().contains(x));
                    // from vec_to_set for set0 we get existence in s0
                    assert(exists|i: int| 0 <= i < s0.len() && s0[i] == x);
                    // from mutual inclusion, s1 contains x
                    assert(s1@.contains(x));
                    // from vec_to_set for set1, s1 contains x implies set1 contains x
                    // show: there exists j with s1[j]==x, so set1.view().contains(x)
                    assert(exists|j: int| 0 <= j < s1.len() && s1[j] == x);
                    assert(set1.view().contains(x));
                };
                // 2) set1 subset set0
                assert(forall|x: u8| set1.view().contains(x) ==> set0.view().contains(x)) by {
                    fix |x: u8|;
                    assume(set1.view().contains(x));
                    assert(exists|i: int| 0 <= i < s1.len() && s1[i] == x);
                    assert(s0@.contains(x));
                    assert(exists|j: int| 0 <= j < s0.len() && s0[j] == x);
                    assert(set0.view().contains(x));
                };
                // from mutual containment of views conclude equality
                assert(set0.view() == set1.view());
            };
            // since we know same is false, mutual inclusion cannot hold
            assert(!( (forall|i: int| 0 <= i < s0.len() ==> s1@.contains(s0[i])) && (forall|i: int| 0 <= i < s1.len() ==> s0@.contains(s1[i])) ));
        }
    }

    same
}
```