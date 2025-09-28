// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn typechar_precedence(c: char) -> nat {
    match c {
        'g' => 0,
        'd' => 1,
        'f' => 2,
        'F' => 3,
        'D' => 4,
        'G' => 5,
        _   => 6,
    }
}

spec fn char_in_typeset(c: char, typeset: Seq<char>) -> bool {
    typeset.contains(c)
}

spec fn filter_chars_in_typeset(typechars: Seq<char>, typeset: Seq<char>) -> Seq<char> {
    typechars.filter(|c: char| char_in_typeset(c, typeset))
}

spec fn min_precedence_char(chars: Seq<char>) -> char
    decreases chars.len()
{
    if chars.len() == 0 {
        'G'
    } else if chars.len() == 1 {
        chars[0]
    } else {
        let first = chars[0];
        let rest_min = min_precedence_char(chars.skip(1));
        if typechar_precedence(first) <= typechar_precedence(rest_min) {
            first
        } else {
            rest_min
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added a helper function to assist with ensuring the result is in the typeset. */
proof fn lemma_min_precedence_char_is_in_seq(chars: Seq<char>)
    requires chars.len() > 0
    ensures chars.contains(min_precedence_char(chars))
    decreases chars.len()
{
    if chars.len() == 1 {
    } else {
        let first = chars[0];
        let rest = chars.skip(1);
        lemma_min_precedence_char_is_in_seq(rest);
        let rest_min = min_precedence_char(rest);
        if typechar_precedence(first) <= typechar_precedence(rest_min) {
        } else {
        }
    }
}

proof fn lemma_min_precedence_char_is_min(chars: Seq<char>)
    requires chars.len() > 0
    ensures
        (forall|c: char| chars.contains(c) ==> typechar_precedence(min_precedence_char(chars)) <= typechar_precedence(c))
    decreases chars.len()
{
    if chars.len() == 1 {
    }
    else {
        let first = chars[0];
        let rest = chars.skip(1);
        lemma_min_precedence_char_is_min(rest);
        let rest_min = min_precedence_char(rest);
        if typechar_precedence(first) <= typechar_precedence(rest_min) {
            assert forall|c: char| chars.contains(c) implies typechar_precedence(min_precedence_char(chars)) <= typechar_precedence(c) by {
                if rest.contains(c) {
                    assert(typechar_precedence(min_precedence_char(rest)) <= typechar_precedence(c));
                    assert(typechar_precedence(min_precedence_char(chars)) <= typechar_precedence(rest_min));
                } else if c == first {
                    assert(typechar_precedence(min_precedence_char(chars)) <= typechar_precedence(first));
                }
            }
        } else {
            assert forall|c: char| chars.contains(c) implies typechar_precedence(min_precedence_char(chars)) <= typechar_precedence(c) by {
                if rest.contains(c) {
                    assert(typechar_precedence(min_precedence_char(rest)) <= typechar_precedence(c));
                    assert(typechar_precedence(min_precedence_char(chars)) <= typechar_precedence(rest_min));
                } else if c == first {
                    assert(typechar_precedence(min_precedence_char(chars)) <= typechar_precedence(rest_min));
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn mintypecode(typechars: Vec<char>, typeset: Vec<char>, default: char) -> (result: char)
    requires typeset@ == seq!['G', 'D', 'F', 'g', 'd', 'f'],
    ensures ({
        let intersection = filter_chars_in_typeset(typechars@, typeset@);

        (intersection.len() == 0 ==> result == default) &&

        (intersection.len() > 0 ==> {

            if intersection.contains('F') && intersection.contains('d') {
                result == 'D'
            } else {

                intersection.contains(result) &&
                (forall|c: char| intersection.contains(c) ==> typechar_precedence(result) <= typechar_precedence(c))
            }
        }) &&

        (intersection.contains(result) || result == default)
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch error by casting intersection.len() to nat before comparison. */
{
    let intersection = filter_chars_in_typeset(typechars@, typeset@);

    if (intersection.len() as nat) == 0 {
        default
    } else {
        if intersection.contains('F') && intersection.contains('d') {
            'D'
        } else {
            proof {
                lemma_min_precedence_char_is_in_seq(intersection);
                lemma_min_precedence_char_is_min(intersection);
            }
            min_precedence_char(intersection)
        }
    }
}
// </vc-code>

}
fn main() {}