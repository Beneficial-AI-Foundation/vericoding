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
/* helper modified by LLM (iteration 5): Added proof lemma for filter correctness */
fn typechar_precedence_exec(c: char) -> (result: u8)
    ensures result as nat == typechar_precedence(c)
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

proof fn lemma_filter_step(typechars: Seq<char>, typeset: Seq<char>, i: int)
    requires
        0 <= i < typechars.len(),
    ensures
        filter_chars_in_typeset(typechars.take(i + 1), typeset) ==
        if char_in_typeset(typechars[i], typeset) {
            filter_chars_in_typeset(typechars.take(i), typeset).push(typechars[i])
        } else {
            filter_chars_in_typeset(typechars.take(i), typeset)
        }
{}
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
    /* code modified by LLM (iteration 5): Fixed loop invariants and bounds checking */
    let mut intersection = Vec::new();
    let mut i: usize = 0;
    while i < typechars.len()
        invariant
            0 <= i <= typechars.len(),
            intersection@ == filter_chars_in_typeset(typechars@.take(i as int), typeset@),
            forall|j: int| 0 <= j < intersection@.len() ==> char_in_typeset(intersection@[j], typeset@),
        decreases typechars.len() - i
    {
        let mut found = false;
        let mut k: usize = 0;
        while k < typeset.len()
            invariant
                0 <= i < typechars.len(),
                0 <= k <= typeset.len(),
                found == exists|j: int| 0 <= j < k && typeset@[j] == typechars@[i as int],
            decreases typeset.len() - k
        {
            if typeset[k] == typechars[i] {
                found = true;
                break;
            }
            k = k + 1;
        }
        
        proof {
            lemma_filter_step(typechars@, typeset@, i as int);
        }
        
        if found {
            intersection.push(typechars[i]);
        }
        i = i + 1;
    }
    assert(typechars@.take(typechars.len() as int) == typechars@);
    assert(intersection@ == filter_chars_in_typeset(typechars@, typeset@));

    if intersection.len() == 0 {
        return default;
    }

    let mut has_F = false;
    let mut has_d = false;
    let mut idx: usize = 0;
    while idx < intersection.len()
        invariant
            0 <= idx <= intersection.len(),
            has_F == exists|j: int| 0 <= j < idx && intersection@[j] == 'F',
            has_d == exists|j: int| 0 <= j < idx && intersection@[j] == 'd',
        decreases intersection.len() - idx
    {
        if intersection[idx] == 'F' {
            has_F = true;
        }
        if intersection[idx] == 'd' {
            has_d = true;
        }
        idx = idx + 1;
    }
    
    if has_F && has_d {
        return 'D';
    }

    let mut min_char = intersection[0];
    let mut min_prec = typechar_precedence_exec(min_char);
    let mut j: usize = 1;
    
    while j < intersection.len()
        invariant
            1 <= j <= intersection.len(),
            intersection@.contains(min_char),
            min_prec as nat == typechar_precedence(min_char),
            forall|k: int| 0 <= k < j ==> typechar_precedence(min_char) <= typechar_precedence(intersection@[k]),
        decreases intersection.len() - j
    {
        let current_prec = typechar_precedence_exec(intersection[j]);
        if current_prec < min_prec {
            min_char = intersection[j];
            min_prec = current_prec;
        }
        j = j + 1;
    }
    
    min_char
}
// </vc-code>

}
fn main() {}