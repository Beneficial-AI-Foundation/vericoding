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
/* helper modified by LLM (iteration 3): provide spec-only min_by_precedence to avoid exec-spec calls */
spec fn min_by_precedence(a: char, b: char) -> char { if typechar_precedence(a) <= typechar_precedence(b) { a } else { b } }
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
{
    /* code modified by LLM (iteration 3): add decreases clause for loop and keep selection logic */
    let mut has_g: bool = false;
    let mut has_d: bool = false;
    let mut has_f: bool = false;
    let mut has_F: bool = false;
    let mut has_D: bool = false;
    let mut has_G: bool = false;

    let mut i: usize = 0;
    while i < typechars.len()
        invariant 0 <= i <= typechars.len()
        decreases typechars.len() - i
    {
        let c = typechars[i];
        if c == 'g' { has_g = true; }
        else if c == 'd' { has_d = true; }
        else if c == 'f' { has_f = true; }
        else if c == 'F' { has_F = true; }
        else if c == 'D' { has_D = true; }
        else if c == 'G' { has_G = true; }
        i = i + 1;
    }

    if !(has_g || has_d || has_f || has_F || has_D || has_G) {
        default
    } else if has_F && has_d {
        'D'
    } else if has_g {
        'g'
    } else if has_d {
        'd'
    } else if has_f {
        'f'
    } else if has_F {
        'F'
    } else if has_D {
        'D'
    } else {
        'G'
    }
}
// </vc-code>

}
fn main() {}