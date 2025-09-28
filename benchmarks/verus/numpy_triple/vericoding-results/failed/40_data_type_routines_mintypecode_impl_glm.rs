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
/* helper modified by LLM (iteration 3): replaced is_empty with len == 0 */
fn find_min_precedence_char(v: Vec<char>) -> (result: char)
    ensures
        v.len() == 0 ==> result == 'G',
        v.len() > 0 ==> {
            v@.contains(result) &&
            forall|i: int| 0 <= i < v.len() ==> typechar_precedence(result) <= typechar_precedence(v@[i])
    }
{
    if v.len() == 0 {
        'G'
    } else {
        let mut min_char = v[0];
        let mut min_prec = typechar_precedence(min_char);
        let mut i = 1;
        while i < v.len()
            invariant
                1 <= i <= v.len(),
                v.contains(&min_char),
                forall|k: int| 0 <= k < i ==> typechar_precedence(min_char) <= typechar_precedence(v@[k]),
        {
            let c = v[i];
            let prec = typechar_precedence(c);
            if prec < min_prec {
                min_char = c;
                min_prec = prec;
            }
            i += 1;
        }
        min_char
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
/* code modified by LLM (iteration 3): replaced is_empty with len == 0 */
{
    let intersection: Vec<char> = typechars.iter().filter(|c| typeset.contains(c)).cloned().collect();

    if intersection.len() == 0 {
        default
    } else if intersection.contains(&'F') && intersection.contains(&'d') {
        'D'
    } else {
        find_min_precedence_char(intersection)
    }
}
// </vc-code>

}
fn main() {}