```vc-helpers
fn contains_substring(s: &str, substring: &str) -> bool
    ensures
        result == (exists|j: int|
            0 <= j <= s@.len() - substring@.len() &&
            s@.subrange(
                j,
                #[trigger] (j + substring@.len()),
            ) == substring@)
{
    let s_len: int = s@.len() as int;
    let sub_len: int = substring@.len() as int;

    // If substring is longer than s, there is no occurrence.
    if sub_len > s_len {
        proof {
            // show there is no valid j in this case
            assert(!exists|k: int|
                0 <= k <= s@.len() - substring@.len() &&
                s@.subrange(
                    k,
                    #[trigger] (k + substring@.len()),
                ) == substring@);
        }
        return false;
    }

    let bound: int = s_len - sub_len;

    let mut j: int = 0;
    while j <= bound
        invariant 0 <= j <= bound + 1
    {
        // If current position matches, return true with a proof of existence.
        if s@.subrange(j, j + substring@.len()) == substring@ {
            proof {
                // j is within [0, bound], and the equality holds, so witness exists.
                assert(0 <= j && j <= bound);
                assert(s@.subrange(j, j + substring@.len()) == substring@);
                assert(exists|k: int|
                    0 <= k <= s@.len() - substring@.len() &&
                    s@.subrange(
                        k,
                        #[trigger] (k + substring@.len()),
                    ) == substring@);
            }
            return true;
        }
        j = j + 1;
    }

    // If loop finished, no position in [0..bound] matched.
    proof {
        assert(!exists|k: int|
            0 <= k <= s@.len() - substring@.len() &&
            s@.subrange(
                k,
                #[trigger] (k + substring@.len()),
            ) == substring@);
    }
    false
}
```

```vc-code
{
    // impl-start
    let mut res: Vec<&'a str> = Vec::new();

    let n: int = strings@.len();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i <= n
        invariant (forall|k: int|
            0 <= k < i ==>
                ((exists|j: int|
                    0 <= j <= strings@[k]@.len() - substring@.len() &&
                    strings@[k]@.subrange(
                        j,
                        #[trigger] (j + substring@.len()),
                    ) == substring@) ==> res@.contains(strings@[k])))
    {
        let s: &str = strings@[i];
        let has: bool = contains_substring(s, substring);
        if has {
            res.push(s);
        }

        // Prove the invariant for i+1
        proof {
            assert(forall|k: int| 0 <= k < i + 1 ==>
                ((exists|j: int|
                    0 <= j <= strings@[k]@.len() - substring@.len() &&
                    strings@[k]@.subrange(
                        j,
                        #[trigger] (j + substring@.len()),
                    ) == substring@) ==> res@.contains(strings@[k])))
            by {
                fix k: int;
                assume Hk: 0 <= k < i + 1;

                if k < i {
                    // use the old invariant for k < i
                    assert((exists|j: int|
                        0 <= j <= strings@[k]@.len() - substring@.len() &&
                        strings@[k]@.subrange(
                            j,
                            #[trigger] (j + substring@.len()),
                        ) == substring@) ==> res@.contains(strings@[k]));
                } else {
                    // k == i
                    // from has we know whether the substring exists in s
                    if has {
                        // contains_substring ensures equivalence, so the existence holds
                        assert(exists|j: int|
                            0 <= j <= s@.len() - substring@.len() &&
                            s@.subrange(
                                j,
                                #[trigger] (j + substring@.len()),
                            ) == substring@);
                        // and since we pushed s, res contains strings@[i]
                        assert(res@.contains(strings@[i]));
                    } else {
                        // contains_substring false implies no such j
                        assert(!exists|j: int|
                            0 <= j <= s@.len() - substring@.len() &&
                            s@.subrange(
                                j,
                                #[trigger] (j + substring@.len()),
                            ) == substring@);
                    }
                    // conclude the implication for k == i
                    assert((exists|j: int|
                        0 <= j <= strings@[k]@.len() - substring@.len() &&
                        strings@[k]@.subrange(
                            j,
                            #[trigger] (j + substring@.len()),
                        ) == substring@) ==> res@.contains(strings@[k]));
                }
            }
        }

        i = i + 1;
    }

    res
    // impl-end
}
```