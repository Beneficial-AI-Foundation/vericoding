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
proof fn decode_in_range(c: int)
    requires 65 <= c <= 90
    ensures 65 <= decode_char_spec(c) <= 90
{
    let a = c - 65;
    assert(0 <= a);
    assert(a <= 25);
    reveal(decode_char_spec);
    // decode_char_spec(c) = ((a + 21) % 26) + 65
    // (a + 21) % 26 is in 0..=25
    assert(0 <= (a + 21) % 26);
    assert((a + 21) % 26 <= 25);
    assert(65 <= ((a + 21) % 26) + 65);
    assert(((a + 21) % 26) + 65 <= 90);
}

proof fn encode_of_decode(c: int)
    requires 65 <= c <= 90
    ensures encode_char_spec(decode_char_spec(c)) == c
{
    let a = c - 65;
    assert(0 <= a);
    assert(a <= 25);
    reveal(decode_char_spec);
    reveal(encode_char_spec);
    // decode_char_spec(c) = ((a + 21) % 26) + 65
    // encode_char_spec(x) = ((x - 65 + 5) % 26) + 65
    // encode_char_spec(decode_char_spec(c)) =
    //    (((a + 21) % 26) + 5) % 26 + 65
    // = ((a + 21 + 5) % 26) + 65 = ((a + 26) % 26) + 65 = (a % 26) + 65
    // since 0 <= a <= 25, a % 26 = a, so result = a + 65 = c
    assert(((a + 21) % 26 + 5) % 26 == a % 26);
    assert(a % 26 == a);
    assert(((a + 21) % 26 + 5) % 26 + 65 == c);
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
    t.reserve(s.len());
    let mut i: int = 0;
    while i < s.len() {
        invariant 0 <= i && i <= s.len();
        invariant t.len() as int == i;
        invariant forall|j: int| 0 <= j < i ==> t[j] == decode_char_spec(s[j] as int);
        {
            let c_u8: u8 = s[i];
            let c_int: int = c_u8 as int;
            // use precondition to know range
            assert(65 <= c_int && c_int <= 90);
            let d: int = decode_char_spec(c_int);
            proof { decode_in_range(c_int); }
            let b: u8 = d as u8;
            proof { encode_of_decode(c_int); }
            // verify encode_char_spec(b as int) == original
            assert(encode_char_spec(b as int) == c_int);
            t.push(b);
            i += 1;
        }
    }
    t
    // impl-end
}
// </vc-code>

fn main() {}
}