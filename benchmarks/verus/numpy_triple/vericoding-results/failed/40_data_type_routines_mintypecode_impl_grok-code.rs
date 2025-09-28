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
/* helper modified by LLM (iteration 5): Changed start parameter to int and updated indices and calculations */
fn filter_chars_exec(typechars: &Vec<char>, typeset: &Vec<char>) -> (result: Vec<char>)
    ensures result@ == filter_chars_in_typeset(typechars@, typeset@)
{
    let mut result = Vec::new();
    let len = typechars.len();
    for i in 0..len
        invariant
            i <= len,
            result.len() <= i,
            forall|k: int| 0 <= k < result.len() ==> result@[k] == typechars@[k] && char_in_typeset(typechars@[k], typeset@),
    {
        if typeset.contains(&typechars[i]) {
            result.push(typechars[i]);
        }
    }
    result
}

fn min_precedence_char_exec(chars: &Vec<char>, start: int) -> (result: char)
    requires 0 <= start <= chars@.len(),
    ensures
        chars@.skip(start).len() == 0 ==> result == 'G',
        chars@.skip(start).len() > 0 ==> result == min_precedence_char(chars@.skip(start)),
    decreases chars@.len() - start
{
    let slen = chars@.len() - start;
    if slen == 0 {
        'G'
    } else {
        let first = chars[start as usize];
        let rest_min = min_precedence_char_exec(chars, start + 1);
        if typechar_precedence(first) <= typechar_precedence(rest_min) {
            first
        } else {
            rest_min
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
/* code modified by LLM (iteration 5): Updated helper calls with corrected parameter types */
{
    let filtered = filter_chars_exec(&typechars, &typeset);
    if filtered.is_empty() {
        default
    } else {
        if filtered.contains(&'F') && filtered.contains(&'d') {
            'D'
        } else {
            min_precedence_char_exec(&filtered, 0)
        }
    }
}
// </vc-code>

}
fn main() {}