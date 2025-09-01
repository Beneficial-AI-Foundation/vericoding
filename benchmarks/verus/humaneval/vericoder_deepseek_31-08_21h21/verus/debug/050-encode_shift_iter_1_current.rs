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
proof fn encode_decode_char_lemma(c: int)
    requires
        65 <= c <= 90,
    ensures
        decode_char_spec(encode_char_spec(c)) == c,
        encode_char_spec(decode_char_spec(c)) == c,
{
    assert(decode_char_spec(encode_char_spec(c)) == c) by {
        assert((c - 65 + 5) % 26 + 65 - 65 + 26 - 5) % 26 + 65 == c);
    };
    assert(encode_char_spec(decode_char_spec(c)) == c) by {
        assert((c - 65 + 26 - 5) % 26 + 65 - 65 + 5) % 26 + 65 == c);
    };
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
    let mut t = Vec::with_capacity(s.len());
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            t.len() == i,
            forall|j: int| 0 <= j < i ==> t@[j] == decode_char_spec(s@[j] as int),
            forall|j: int| 0 <= j < i ==> encode_char_spec(t@[j] as int) == s@[j] as int,
    {
        proof {
            let idx = i;
            assert(65 <= s[idx] <= 90) by {
                assert(0 <= idx < s.len() ==> 65 <= s@[idx] <= 90);
            };
        }
        let decoded = ((s[i] as int - 65 + 21) % 26 + 65) as u8;
        t.push(decoded);
        proof {
            encode_decode_char_lemma(s@[i] as int);
            assert(t@[i] == decode_char_spec(s@[i] as int));
            assert(encode_char_spec(t@[i] as int) == s@[i] as int);
        }
        i += 1;
    }
    t
}
// </vc-code>

fn main() {}
}