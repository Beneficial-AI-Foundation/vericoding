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
/* helper modified by LLM (iteration 3): proves min_precedence_char returns an element of the sequence */
fn min_precedence_char_in(chars: Seq<char>)
    requires
        chars.len() > 0usize,
    ensures
        chars.contains(min_precedence_char(chars)),
    decreases
        chars.len()
{
    if chars.len() == 1usize {
        // base case: the only element is the minimum
    } else {
        let first = chars.index(0usize);
        let rest = chars.skip(1usize);
        let rest_min = min_precedence_char(rest);
        if typechar_precedence(first) <= typechar_precedence(rest_min) {
            // min_precedence_char(chars) == first, and first is in chars
        } else {
            // min_precedence_char(chars) == rest_min, apply induction on rest
            min_precedence_char_in(rest);
        }
    }
}

/* helper modified by LLM (iteration 3): proves min_precedence_char has minimal precedence among the sequence */
fn min_precedence_char_minimal(chars: Seq<char>)
    requires
        chars.len() > 0usize,
    ensures
        forall |c: char| chars.contains(c) ==> typechar_precedence(min_precedence_char(chars)) <= typechar_precedence(c),
    decreases
        chars.len()
{
    if chars.len() == 1usize {
        // single element is trivially minimal
    } else {
        let first = chars.index(0usize);
        let rest = chars.skip(1usize);
        let rest_min = min_precedence_char(rest);
        if typechar_precedence(first) <= typechar_precedence(rest_min) {
            // min_precedence_char(chars) == first; need induction to relate rest elements
            min_precedence_char_minimal(rest);
        } else {
            // min_precedence_char(chars) == rest_min; apply induction on rest
            min_precedence_char_minimal(rest);
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
{
    /* code modified by LLM (iteration 3): compute minimal type code from intersection or default */
    let intersection = filter_chars_in_typeset(typechars@, typeset@);

    if intersection.len() == 0usize {
        default
    } else {
        if intersection.contains('F') && intersection.contains('d') {
            'D'
        } else {
            let res = min_precedence_char(intersection);
            proof {
                min_precedence_char_in(intersection);
                min_precedence_char_minimal(intersection);
            }
            res
        }
    }
}

// </vc-code>

}
fn main() {}