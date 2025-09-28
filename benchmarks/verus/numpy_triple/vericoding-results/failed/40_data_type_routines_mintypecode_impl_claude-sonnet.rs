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
proof fn lemma_min_precedence_char_correct(chars: Seq<char>)
    requires chars.len() > 0,
    ensures
        chars.contains(min_precedence_char(chars)),
        forall|c: char| chars.contains(c) ==> typechar_precedence(min_precedence_char(chars)) <= typechar_precedence(c),
    decreases chars.len()
{
    if chars.len() == 1 {
        assert(chars.contains(chars[0]));
    } else {
        let first = chars[0];
        let rest = chars.skip(1);
        lemma_min_precedence_char_correct(rest);
        let rest_min = min_precedence_char(rest);
        
        if typechar_precedence(first) <= typechar_precedence(rest_min) {
            assert(min_precedence_char(chars) == first);
        } else {
            assert(min_precedence_char(chars) == rest_min);
        }
    }
}

proof fn lemma_filter_preserves_contains(typechars: Seq<char>, typeset: Seq<char>, c: char)
    requires
        char_in_typeset(c, typeset),
        typechars.contains(c),
    ensures filter_chars_in_typeset(typechars, typeset).contains(c)
{
}

/* helper modified by LLM (iteration 5): added helper to check if character is in typeset using vec indexing */
fn char_in_vec(c: char, typeset: &Vec<char>) -> (result: bool)
    ensures result == typeset@.contains(c)
{
    let mut i = 0;
    while i < typeset.len()
        invariant
            0 <= i <= typeset.len(),
            !typeset@.take(i as int).contains(c),
    {
        if typeset[i] == c {
            return true;
        }
        i += 1;
    }
    false
}

/* helper modified by LLM (iteration 5): fixed compute_precedence to return nat values without invalid suffix */
fn compute_precedence(c: char) -> (result: nat)
    ensures result == typechar_precedence(c)
{
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
    /* code modified by LLM (iteration 5): use compute_precedence exec function without nat suffix errors */
    let mut filtered: Vec<char> = Vec::new();
    
    for i in 0..typechars.len()
        invariant
            typeset@ == seq!['G', 'D', 'F', 'g', 'd', 'f'],
            filtered@ == filter_chars_in_typeset(typechars@.take(i as int), typeset@),
    {
        let c = typechars[i];
        if char_in_vec(c, &typeset) {
            filtered.push(c);
        }
    }
    
    if filtered.len() == 0 {
        return default;
    }
    
    let has_F = char_in_vec('F', &filtered);
    let has_d = char_in_vec('d', &filtered);
    
    if has_F && has_d {
        return 'D';
    }
    
    proof {
        lemma_min_precedence_char_correct(filtered@);
    }
    
    let mut min_char = filtered[0];
    for i in 1..filtered.len()
        invariant
            filtered@ == filter_chars_in_typeset(typechars@, typeset@),
            filtered@.contains(min_char),
            forall|j: int| 0 <= j < i ==> typechar_precedence(min_char) <= typechar_precedence(filtered@[j]),
    {
        if compute_precedence(filtered[i]) < compute_precedence(min_char) {
            min_char = filtered[i];
        }
    }
    
    min_char
}
// </vc-code>

}
fn main() {}