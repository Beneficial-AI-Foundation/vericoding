use vstd::prelude::*;

verus! {

spec fn encode_char_spec(c: int) -> (result:int)
    recommends
        65 <= c <= 90,
{
    (c - 65 + 5) % 26 + 65
}
// pure-end
spec fn decode_char_spec(c: int) -> (result:int)
    recommends
        65 <= c <= 90,
{
    (c - 65 + 26 - 5) % 26 + 65
}
// pure-end

// <vc-helpers>
proof fn encode_decode_inverse(c: int)
    requires 65 <= c <= 90,
    ensures encode_char_spec(decode_char_spec(c)) == c,
{
    // Unfold definitions
    assert(decode_char_spec(c) == (c - 65 + 26 - 5) % 26 + 65);
    // Let d = decode_char_spec(c) - 65
    let d = decode_char_spec(c) - 65;
    assert(d == (c - 65 + 26 - 5) % 26);
    // Unfold encode on decode
    assert(encode_char_spec(decode_char_spec(c)) == (d + 5) % 26 + 65);

    // Show ((c-65+26-5)%26 + 5) % 26 == (c-65) % 26
    assert(((c - 65 + 26 - 5) % 26 + 5) % 26 == (c - 65 + 26 - 5 + 5) % 26);
    assert((c - 65 + 26 - 5 + 5) % 26 == (c - 65 + 26) % 26);
    assert((c - 65 + 26) % 26 == (c - 65) % 26);

    // From 65 <= c <= 90 we have 0 <= c-65 < 26
    assert(0 <= c - 65 && c - 65 < 26);
    assert((c - 65) % 26 == c - 65);

    // Chain equalities to conclude
    assert(encode_char_spec(decode_char_spec(c)) == (c - 65) % 26 + 65);
    assert((c - 65) % 26 + 65 == c);
    // final
    assert(encode_char_spec(decode_char_spec(c)) == c);
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn decode_shift(s: &Vec<u8>) -> (t: Vec<u8>)
    // pre-conditions-start
    requires
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> 65 <= s[i] <= 90,
    // pre-conditions-end
    // post-conditions-start
    ensures
        s.len() == t.len(),
        forall|i: int| #![auto] 0 <= i < t.len() ==> t[i] == decode_char_spec(s[i] as int),
        forall|i: int| #![auto] 0 <= i < t.len() ==> encode_char_spec(t[i] as int) == s[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut t: Vec<u8> = Vec::new();
    let mut i: int = 0;
    while i < s.len()
        invariant { 0 <= i && i <= s.len() },
        invariant { t.len() == i },
        invariant { forall|j: int| 0 <= j && j < i ==> (t[j] as int) == decode_char_spec(s[j] as int) },
    {
        let x: int = s[i] as int;
        let y: int = decode_char_spec(x);
        let b: u8 = y as u8;
        t.push(b);
        // after push, t[i] is defined and equals b
        assert(t[i] as int == decode_char_spec(s[i] as int));
        i = i + 1;
    }

    // Prove the postconditions
    proof {
        // lengths equal
        assert(t.len() == s.len());

        // For all positions, t[j] as int == decode_char_spec(s[j] as int)
        assert(forall|j: int| 0 <= j && j < t.len() ==> (t[j] as int) == decode_char_spec(s[j] as int));

        // For all positions, encode_char_spec(t[j] as int) == s[j] (as int)
        assert(forall|j: int| 0 <= j && j < t.len() ==>
            {
                // fix j
                let sj_int: int = s[j] as int;
                // from precondition 65 <= s[j] <= 90
                assert(65 <= sj_int && sj_int <= 90);
                // t[j] as int == decode_char_spec(s[j] as int)
                assert((t[j] as int) == decode_char_spec(s[j] as int));
                // apply lemma
                encode_decode_inverse(sj_int);
                // encode(decode(sj)) == sj
                assert(encode_char_spec(decode_char_spec(sj_int)) == sj_int);
                // since t[j] == decode(sj), we have encode(t[j]) == sj
                assert(encode_char_spec(t[j] as int) == sj_int);
                true
            }
        );
    }

    t
    // impl-end
}
// </vc-code>

fn main() {}
}