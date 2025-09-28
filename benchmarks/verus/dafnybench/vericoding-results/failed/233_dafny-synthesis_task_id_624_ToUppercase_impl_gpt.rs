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
proof fn lemma_shift_minus_32_lower_case(c: char)
    requires
        is_lower_case(c)
    ensures
        is_lower_upper_pair(c, shift_minus_32(c))
{
    let ci = c as int;
    let x = ci - 32;
    assert(97 <= ci <= 122);
    assert(65 <= x && x <= 90);
    assert(0 < 128);
    assert(0 <= x && x < 128);
    assert((x % 128) == x);
    assert((shift_minus_32(c) as int) == (x % 128));
    assert((shift_minus_32(c) as int) == x);
    assert(ci == (shift_minus_32(c) as int) + 32);
}

spec fn idx(s: Seq<char>, i: int) -> char {
    s[i]
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
    proof {
        v = Seq::new(s.len(), |i: int|
            if is_lower_case(idx(s, i)) {
                shift_minus_32(idx(s, i))
            } else {
                idx(s, i)
            }
        );

        assert forall|i: int| 0 <= i && i < s.len() implies
            if is_lower_case(s[i]) {
                is_lower_upper_pair(s[i], v[i])
            } else {
                v[i] == s[i]
            } by {
                if 0 <= i && i < s.len() {
                    assert(v[i] == if is_lower_case(idx(s, i)) { shift_minus_32(idx(s, i)) } else { idx(s, i) });
                    if is_lower_case(s[i]) {
                        lemma_shift_minus_32_lower_case(s[i]);
                        assert(idx(s, i) == s[i]);
                        assert(v[i] == shift_minus_32(s[i]));
                        assert(is_lower_upper_pair(s[i], v[i]));
                    } else {
                        assert(idx(s, i) == s[i]);
                        assert(v[i] == s[i]);
                    }
                }
            };

        assert forall|c: char| is_lower_case(c) implies is_lower_upper_pair(c, shift_minus_32(c)) by {
            if is_lower_case(c) {
                lemma_shift_minus_32_lower_case(c);
            }
        };
    }
}
// </vc-code>

fn main() {
}

}