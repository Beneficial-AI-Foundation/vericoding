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
spec fn to_upper_char(c: char) -> char {
    if is_lower_case(c) {
        shift_minus_32(c)
    } else {
        c
    }
}

proof fn to_upper_char_spec_lemma(c: char)
    ensures
        if is_lower_case(c) {
            is_lower_upper_pair(c, to_upper_char(c))
        } else {
            to_upper_char(c) == c
        }
{
}

proof fn to_upper_char_spec_lemma_for_seq(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        if is_lower_case(s[i]) {
            is_lower_upper_pair(s[i], to_upper_char(s[i]))
        } else {
            to_upper_char(s[i]) == s[i]
        }
{
    to_upper_char_spec_lemma(s[i]);
}

proof fn map_lemma(s: Seq<char>)
    ensures
        (Seq::new(s.len(), |i| to_upper_char(s[i]))).len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if is_lower_case(s[i]) {
                is_lower_upper_pair(s[i], (Seq::new(s.len(), |i| to_upper_char(s[i])))[i])
            } else {
                (Seq::new(s.len(), |i| to_upper_char(s[i])))[i] == s[i]
            }
{
    assert forall|i: int| 0 <= i < s.len() implies 
        if is_lower_case(s[i]) {
            is_lower_upper_pair(s[i], (Seq::new(s.len(), |i| to_upper_char(s[i])))[i])
        } else {
            (Seq::new(s.len(), |i| to_upper_char(s[i])))[i] == s[i]
        } by {
        to_upper_char_spec_lemma_for_seq(s, i);
    };
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
    let mut v = Vec::<char>::new();
    let mut j: nat = 0;
    while j < s.len() as nat
        invariant
            j <= s.len() as nat,
            v@.len() == j as usize,
            forall|i: int| 0 <= i < j ==> 
                if is_lower_case(s[i]) {
                    is_lower_upper_pair(s[i], v@[i as usize])
                } else {
                    v@[i as usize] == s[i]
                },
    {
        let c = s[j as usize];
        let upper_c = if is_lower_case(c) {
            shift_minus_32(c)
        } else {
            c
        };
        proof {
            to_upper_char_spec_lemma(c);
        }
        v.push(upper_c);
        j = j + 1;
    }
    Seq::from_vec(v)
}
// </vc-code>

fn main() {
}

}