use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> bool {
    97 <= c as int <= 122
}

spec fn is_lower_upper_pair(c: char, C: char) -> bool {
    (c as int) == (C as int) + 32
}

spec fn shift_minus_32(c: char) -> char {
    ((c as int - 32) % 128) as char
}

// <vc-helpers>
proof fn shift_minus_32_correct(c: char)
    requires
        is_lower_case(c)
    ensures
        is_lower_upper_pair(c, shift_minus_32(c))
{
    let ci = c as int;
    // from is_lower_case
    assert(97 <= ci && ci <= 122);
    let diff = ci - 32;
    // diff is in [65,90], hence within 0..128
    assert(0 <= diff && diff < 128);
    // expand definition of shift_minus_32
    assert((shift_minus_32(c) as int) == ((ci - 32) % 128));
    // since 0 <= diff < 128, (ci - 32) % 128 == diff
    assert(((ci - 32) % 128) == diff);
    // therefore shift_minus_32(c) as int == diff, so adding 32 yields ci
    assert((shift_minus_32(c) as int) + 32 == ci);
}
// </vc-helpers>

// <vc-spec>
fn to_uppercase(s: Seq<char>) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if is_lower_case(s[i]) {
                is_lower_upper_pair(s[i], v[i])
            } else {
                v[i] == s[i]
            }
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<char> = Vec::new();
    let mut i: nat = 0;
    while i < s.len()
        invariant i <= s.len(),
        invariant v.len() == i,
        invariant forall |j: nat| j < i ==>
            (if is_lower_case(s[j]) { is_lower_upper_pair(s[j], v[j]) } else { v[j] == s[j] }),
        decreases s.len() - i
    {
        let c = s[i];
        if is_lower_case(c) {
            let newc = shift_minus_32(c);
            v.push(newc);
            proof {
                shift_minus_32_correct(c);
            }
            // establish the property for the newly pushed element
            assert(v[i] == newc);
            assert(is_lower_upper_pair(c, v[i]));
        } else {
            v.push(c);
            // establish the property for the newly pushed element
            assert(v[i] == c);
        }
        i = i + 1;
    }
    v.to_seq()
}
// </vc-code>

fn main() {
}

}