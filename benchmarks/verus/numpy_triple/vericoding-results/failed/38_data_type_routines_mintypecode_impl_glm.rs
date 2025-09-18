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
/* helper modified by LLM (iteration 3): change return type from nat to u8 to fix compilation error */
fn exec_typechar_precedence(c: char) -> u8 {
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

proof fn typechar_precedence_eq(c: char)
    ensures (exec_typechar_precedence(c) as nat) == typechar_precedence(c)
{
    match c {
        'g' => { assert(exec_typechar_precedence(c) == 0 && (0 as nat) == typechar_precedence(c)); },
        'd' => { assert(exec_typechar_precedence(c) == 1 && (1 as nat) == typechar_precedence(c)); },
        'f' => { assert(exec_typechar_precedence(c) == 2 && (2 as nat) == typechar_precedence(c)); },
        'F' => { assert(exec_typechar_precedence(c) == 3 && (3 as nat) == typechar_precedence(c)); },
        'D' => { assert(exec_typechar_precedence(c) == 4 && (4 as nat) == typechar_precedence(c)); },
        'G' => { assert(exec_typechar_precedence(c) == 5 && (5 as nat) == typechar_precedence(c)); },
        _   => { assert(exec_typechar_precedence(c) == 6 && (6 as nat) == typechar_precedence(c)); },
    }
}

/* helper modified by LLM (iteration 5): add exec_contains function to replace unsupported contains method */
fn exec_contains(vec: &Vec<char>, c: char) -> bool {
    let mut found = false;
    let mut i = 0;
    while i < vec.len() {
        if vec[i] == c {
            found = true;
            break;
        }
        i += 1;
    }
    found
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
/* code modified by LLM (iteration 5): replace contains method calls with exec_contains */
{
    let mut intersection: Vec<char> = Vec::new();
    for i in 0..typechars.len() {
        let c = typechars[i];
        if exec_contains(&typeset, c) {
            intersection.push(c);
        }
    }

    if intersection.is_empty() {
        return default;
    }

    if exec_contains(&intersection, 'F') && exec_contains(&intersection, 'd') {
        return 'D';
    }

    let mut min_char = intersection[0];
    let mut min_prec = exec_typechar_precedence(min_char);
    for i in 1..intersection.len() {
        let c = intersection[i];
        let prec = exec_typechar_precedence(c);
        if prec < min_prec {
            min_char = c;
            min_prec = prec;
        }
    }
    min_char
}
// </vc-code>

}
fn main() {}