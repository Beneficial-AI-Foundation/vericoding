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
/* helper modified by LLM (iteration 5): Added missing helper functions and lemmas */
proof fn lemma_min_precedence_is_in_seq(chars: Seq<char>)
    requires chars.len() > 0,
    ensures chars.contains(min_precedence_char(chars)),
    decreases chars.len(),
{
    if chars.len() == 1 {
        assert(chars.contains(chars[0]));
    } else {
        lemma_min_precedence_is_in_seq(chars.skip(1));
        assert(chars.skip(1).contains(min_precedence_char(chars.skip(1))));
        assert(chars.contains(chars[0]));
    }
}

proof fn lemma_min_precedence_is_minimal(chars: Seq<char>)
    requires chars.len() > 0,
    ensures forall|c: char| chars.contains(c) ==> typechar_precedence(min_precedence_char(chars)) <= typechar_precedence(c),
    decreases chars.len(),
{
    if chars.len() == 1 {
        assert(min_precedence_char(chars) == chars[0]);
    } else {
        lemma_min_precedence_is_minimal(chars.skip(1));
        let first = chars[0];
        let rest_min = min_precedence_char(chars.skip(1));
        assert(forall|c: char| chars.skip(1).contains(c) ==> typechar_precedence(rest_min) <= typechar_precedence(c));
    }
}

fn exec_min_precedence_char(chars: &Vec<char>) -> (result: char)
    requires chars@.len() > 0,
    ensures result == min_precedence_char(chars@),
{
    if chars.len() == 1 {
        return chars[0];
    }
    
    let mut min_char = chars[0];
    let mut min_prec = typechar_precedence(chars[0]);
    let mut i: usize = 1;
    
    while i < chars.len()
        invariant
            1 <= i <= chars.len(),
            min_prec == typechar_precedence(min_char),
            chars@.take(i as int).contains(min_char),
            forall|j: nat| j < i ==> typechar_precedence(min_char) <= typechar_precedence(chars@[j as int]),
            min_char == min_precedence_char(chars@.take(i as int)),
        decreases chars.len() - i,
    {
        let c = chars[i];
        let prec = typechar_precedence(c);
        if prec < min_prec {
            min_char = c;
            min_prec = prec;
        }
        i = i + 1;
    }
    
    proof {
        assert(chars@.take(chars@.len() as int) == chars@);
    }
    
    min_char
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
    /* code modified by LLM (iteration 5): Fixed function calls to use the added helper functions */
    let mut intersection_vec: Vec<char> = vec![];
    let mut i: usize = 0;
    
    while i < typechars.len()
        invariant
            0 <= i <= typechars.len(),
            intersection_vec@ == filter_chars_in_typeset(typechars@.take(i as int), typeset@),
            forall|j: nat| j < intersection_vec@.len() ==> typeset@.contains(intersection_vec@[j as int]),
        decreases typechars.len() - i
    {
        let c = typechars[i];
        let mut found = false;
        let mut j: usize = 0;
        
        while j < typeset.len()
            invariant
                0 <= j <= typeset.len(),
                found <==> typeset@.take(j as int).contains(c),
            decreases typeset.len() - j
        {
            if typeset[j] == c {
                found = true;
            }
            j = j + 1;
        }
        
        if found {
            intersection_vec.push(c);
        }
        
        i = i + 1;
    }
    
    if intersection_vec.len() == 0 {
        return default;
    }
    
    let mut has_F = false;
    let mut has_d = false;
    let mut k: usize = 0;
    
    while k < intersection_vec.len()
        invariant
            0 <= k <= intersection_vec.len(),
            has_F <==> intersection_vec@.take(k as int).contains('F'),
            has_d <==> intersection_vec@.take(k as int).contains('d'),
        decreases intersection_vec.len() - k
    {
        if intersection_vec[k] == 'F' {
            has_F = true;
        }
        if intersection_vec[k] == 'd' {
            has_d = true;
        }
        k = k + 1;
    }
    
    if has_F && has_d {
        return 'D';
    }
    
    proof {
        lemma_min_precedence_is_in_seq(intersection_vec@);
        lemma_min_precedence_is_minimal(intersection_vec@);
    }
    
    let result = exec_min_precedence_char(&intersection_vec);
    result
}
// </vc-code>

}
fn main() {}