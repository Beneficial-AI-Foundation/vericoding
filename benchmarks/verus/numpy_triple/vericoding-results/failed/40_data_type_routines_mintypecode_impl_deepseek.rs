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
/* helper modified by LLM (iteration 5): Fix compilation error with comma separator and refine proof function */

spec fn min_precedence_char_nonempty(chars: Seq<char>) -> char
    requires chars.len() > 0,
    ensures
        chars.contains(result),
        forall|c: char| chars.contains(c) ==> typechar_precedence(result) <= typechar_precedence(c)
{
    if chars.len() == 1 {
        chars[0]
    } else {
        let first = chars[0];
        let rest_min = min_precedence_char_nonempty(chars.skip(1));
        if typechar_precedence(first) <= typechar_precedence(rest_min) {
            first
        } else {
            rest_min
        }
    }
}

spec fn intersection_contains_F_and_d(s: Seq<char>) -> bool {
    s.contains('F') && s.contains('d')
}

proof fn min_precedence_char_properties(chars: Seq<char>)
    requires chars.len() > 0,
    ensures
        let min_char = min_precedence_char_nonempty(chars),
        (intersection_contains_F_and_d(chars) ==> typechar_precedence(min_char) >= typechar_precedence('d')),
        (intersection_contains_F_and_d(chars) ==> min_char != 'F')
    decreases chars.len()
{
    if chars.len() > 1 {
        min_precedence_char_properties(chars.skip(1));
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
{
    /* code modified by LLM (iteration 5): Fixed function call syntax with comma separator */
    let intersection_filtered: Vec<char> = typechars.into_iter().filter(|&c| char_in_typeset(c, typeset@)).collect();
    
    if intersection_filtered.is_empty() {
        default
    } else if intersection_filtered.contains(&'F') && intersection_filtered.contains(&'d') {
        'D'
    } else {
        let min_char = min_precedence_char(intersection_filtered@);
        proof { min_precedence_char_properties(intersection_filtered@); }
        min_char
    }
}
// </vc-code>

}
fn main() {}