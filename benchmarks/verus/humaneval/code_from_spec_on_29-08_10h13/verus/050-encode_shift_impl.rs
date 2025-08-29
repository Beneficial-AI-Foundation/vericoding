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
    requires 65 <= c <= 90
    ensures decode_char_spec(encode_char_spec(c)) == c
{
    let encoded = encode_char_spec(c);
    let decoded = decode_char_spec(encoded);
    assert(encoded == (c - 65 + 5) % 26 + 65);
    assert(decoded == (encoded - 65 + 26 - 5) % 26 + 65);
    assert(decoded == ((c - 65 + 5) % 26 + 65 - 65 + 26 - 5) % 26 + 65);
    assert(decoded == ((c - 65 + 5) % 26 + 21) % 26 + 65);
    assert(decoded == ((c - 65 + 5 + 21) % 26) % 26 + 65);
    assert(decoded == (c - 65 + 26) % 26 + 65);
    assert(decoded == (c - 65) % 26 + 65);
    assert(decoded == c - 65 + 65) by {
        assert(0 <= c - 65 < 26);
    };
}

proof fn char_bounds_preserved(c: int)
    requires 65 <= c <= 90
    ensures 65 <= encode_char_spec(c) <= 90
{
    let result = encode_char_spec(c);
    assert(0 <= c - 65 <= 25);
    assert(5 <= c - 65 + 5 <= 30);
    assert(0 <= (c - 65 + 5) % 26 <= 25);
    assert(65 <= (c - 65 + 5) % 26 + 65 <= 90);
}

exec fn encode_char(c: u8) -> (result: u8)
    requires 65 <= c <= 90
    ensures result == encode_char_spec(c as int) as u8
    ensures 65 <= result <= 90
{
    proof {
        char_bounds_preserved(c as int);
    }
    let shifted = (c - 65 + 5) % 26 + 65;
    shifted
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def encode_shift(s: String) -> String"
docstring: |
returns encoded string by shifting every character by 5 in the alphabet.
test_cases:
- input: abc
expected_output: fgh
- input: xyz
expected_output: cde
- input: aaa
expected_output: fff
*/
// </vc-description>

// <vc-spec>
fn encode_shift(s: Vec<u8>) -> (result: Vec<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> 65 <= s@[i] <= 90
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> result@[i] == encode_char_spec(s@[i] as int) as u8,
        forall|i: int| 0 <= i < result.len() ==> 65 <= result@[i] <= 90
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == encode_char_spec(s@[j] as int) as u8,
            forall|j: int| 0 <= j < result.len() ==> 65 <= result@[j] <= 90,
            forall|j: int| 0 <= j < s.len() ==> 65 <= s@[j] <= 90
    {
        /* code modified by LLM (iteration 5): use encode_char helper function */
        let encoded_char = encode_char(s[i]);
        result.push(encoded_char);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}