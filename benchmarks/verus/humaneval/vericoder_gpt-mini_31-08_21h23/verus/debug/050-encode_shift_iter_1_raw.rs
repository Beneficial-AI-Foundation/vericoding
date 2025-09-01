```vc-helpers
// <vc-helpers>
proof fn decode_in_range(c: int)
    requires 65 <= c <= 90
    ensures 65 <= decode_char_spec(c) <= 90
{
    let k = c - 65;
    assert(0 <= k && k <= 25);

    // decode_char_spec(c) = ((k + 21) % 26) + 65
    assert(decode_char_spec(c) == ((k + 21) % 26) + 65);

    if k <= 4 {
        // k + 21 < 26, so (k + 21) % 26 == k + 21
        assert((k + 21) < 26);
        assert(((k + 21) % 26) == (k + 21));
        assert(decode_char_spec(c) == (k + 21) + 65);
        assert(65 <= decode_char_spec(c) && decode_char_spec(c) <= 90);
    } else {
        // k >= 5, so k + 21 >= 26, and (k + 21) % 26 == k + 21 - 26 == k - 5
        assert((k + 21) >= 26);
        assert(((k + 21) % 26) == (k + 21 - 26));
        assert(decode_char_spec(c) == (k - 5) + 65);
        assert(65 <= decode_char_spec(c) && decode_char_spec(c) <= 90);
    }
}

proof fn decode_encode_inverse(c: int)
    requires 65 <= c <= 90
    ensures encode_char_spec(decode_char_spec(c)) == c
{
    let k = c - 65;
    assert(0 <= k && k <= 25);

    // decode_char_spec(c) = ((k + 21) % 26) + 65
    assert(decode_char_spec(c) == ((k + 21) % 26) + 65);

    if k <= 4 {
        // (k + 21) < 26 so (k + 21) % 26 == k + 21
        assert((k + 21) < 26);
        assert(((k + 21) % 26) == (k + 21));
        // decode = (k+21)+65
        let d = (k + 21) + 65;
        // encode_char_spec(d) = ((d - 65 + 5) % 26) + 65 = ((k + 21 + 5) % 26) + 65 = ((k + 26) % 26) + 65 = k + 65 = c
        assert(encode_char_spec(d) == ((k + 26) % 26) + 65);
        // since 0 <= k <= 25, (k + 26) % 26 == k
        assert(((k + 26) % 26) == k);
        assert(encode_char_spec(d) == k + 65);
        assert(encode_char_spec(d) == c);
    } else {
        // k >= 5, so (k + 21) % 26 == k - 5
        assert((k + 21) >= 26);
        assert(((k + 21) % 26) == (k + 21 - 26));
        // decode = (k - 5) + 65
        let d = (k - 5) + 65;
        // encode_char_spec(d) = ((d - 65 + 5) % 26) + 65 = ((k - 5 + 5) % 26) + 65 = (k % 26) + 65 = k + 65 = c
        assert(encode_char_spec(d) == ((k % 26) + 65));
        // since 0 <= k <= 25, k % 26 == k
        assert((k % 26) == k);
        assert(encode_char_spec(d) == k + 65);
        assert(encode_char_spec(d) == c);
    }
}
// </vc-helpers>
```

```vc-code
{
    // impl-start
    let n = s.len();
    let mut t = Vec::<u8>::new();
    t.reserve(n);
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            t.len() == i,
            forall|j: int| 0 <= j < i ==> (t[j] as int) == decode_char_spec(s[j] as int),
    {
        let b = s[i];
        let dec = decode_char_spec(b as int);
        proof {
            decode_in_range(b as int);
        }
        assert(65 <= dec && dec <= 90);
        t.push(dec as u8);
        i = i + 1;
    }

    // Prove encode property for all elements
    assert(forall|j: int| 0 <= j < n ==> encode_char_spec(t[j] as int) == s[j]) by {
        fix j;
        assume Hj: 0 <= j && j < n;
        // from loop invariant at termination we have t[j] as int == decode_char_spec(s[j])
        assert((t[j] as int) == decode_char_spec(s[j] as int));
        // apply lemma: encode_char_spec(decode_char_spec(s[j])) == s[j]
        decode_encode_inverse(s[j] as int);
        assert(encode_char_spec(decode_char_spec(s[j] as int)) == s[j]);
        assert(encode_char_spec(t[j] as int) == s[j]);
    };

    t
    // impl-end
}
```