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
proof fn casting_lemma(x: int)
    requires 0 <= x < 128
    ensures (x as char) as int == x
{
    assert((x as char) as int == x);
}

#[doc(hidden)]
proof fn helper_char_to_int_range(c: char)
    ensures 0 <= (c as int) < 128
{
    assert((c as int) < 128);
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
    let n = s.len();
    let v = Seq::new(n, |i: int| {
        let c = s[i];
        if is_lower_case(c) {
            shift_minus_32(c)
        } else {
            c
        }
    });

    proof {
        assert forall |i: int| 
            #![trigger v[i]] 
            #![trigger is_lower_case(s[i])]
            0 <= i < n 
            implies 
                if is_lower_case(s[i]) {
                    is_lower_upper_pair(s[i], v[i])
                } else {
                    v[i] == s[i]
                }
        by {
            let c = s[i];
            helper_char_to_int_range(c);
            if is_lower_case(c) {
                let C_upper = v[i];
                assert(is_lower_upper_pair(c, C_upper));
                assert(c as int == C_upper as int + 32);
            } else {
                assert(v[i] == c);
            }
        };
    }

    v
}
// </vc-code>

fn main() {
}

}