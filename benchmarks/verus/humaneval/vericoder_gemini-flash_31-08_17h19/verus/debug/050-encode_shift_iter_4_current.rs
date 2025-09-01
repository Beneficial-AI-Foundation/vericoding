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
#[verifier::loop_isolation(false)]
fn decode_char_helper(c: u8) -> (result: u8)
    requires
        65 <= c as int <= 90,
    ensures
        result as int == decode_char_spec(c as int),
{
    let val_int: int = c as int;
    let decoded_val_int: int = (val_int - 65 + 26 - 5) % 26 + 65;
    decoded_val_int as u8
}

#[verifier::loop_isolation(false)]
proof fn encode_decode_inverse_proof(c_val: int)
    requires
        65 <= c_val <= 90,
    ensures
        encode_char_spec(decode_char_spec(c_val)) == c_val,
{
    let decoded = decode_char_spec(c_val);
    let encoded = encode_char_spec(decoded);

    assert(encoded == c_val) by {
        // We know that for any integer N, (N % M + M) % M == N % M.
        // Let N = c_val - 65 and M = 26.
        // decoded_char_spec transforms N to (N + 26 - 5) % 26.
        // encode_char_spec transforms this back.
        // So we need to show: ((c_val - 65 + 26 - 5) % 26 + 5) % 26 == (c_val - 65) % 26
        // Let X = c_val - 65. We want to show: ( (X + 21) % 26 + 5 ) % 26 == X % 26.
        assert((c_val - 65 + 26 - 5 + 5 ) % 26 == (c_val - 65 + 26) % 26) by {
            assert((c_val - 65 + 26 - 5 + 5) % 26 == (c_val - 65 + 26) % 26);
        }
        assert((c_val - 65 + 26) % 26 == (c_val - 65) % 26);
        assert(encode_char_spec(decode_char_spec(c_val)) == c_val);
    }
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
    let mut t: Vec<u8> = Vec::new();
    let mut i: int = 0;

    while i < s.len()
        invariant
            0 <= i <= s.len(),
            t.len() == i,
            forall|j: int| 0 <= j < i ==> t[j] as int == decode_char_spec(s[j] as int),
            forall|j: int| 0 <= j < i ==> encode_char_spec(t[j] as int) == s[j],
    {
        let original_char: u8 = s[i as nat]; // Cast i to nat for indexing
        let decoded_char: u8 = decode_char_helper(original_char);
        t.push(decoded_char);

        proof {
            // Need to assert the properties for the newly pushed element
            encode_decode_inverse_proof(original_char as int);
            assert(t.last().is_Some()); // Verify that push was successful
            let last_val = t.last().unwrap();
            assert(last_val as int == decoded_char as int); // Ensure it's the right value
            assert(encode_char_spec(last_val as int) == original_char as int);
            assert(encode_char_spec(t[i as nat] as int) == s[i as nat]);
        }
        i = i + 1;
    }
    t
}
// </vc-code>

fn main() {}
}