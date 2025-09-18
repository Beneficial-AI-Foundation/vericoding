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
/* helper modified by LLM (iteration 5): Fixed proof lemma signatures and ensured proper syntax */
proof fn lemma_filter_loop_invariant(filtered: Vec<char>, typechars: Seq<char>, typeset: Seq<char>, i: int)
    requires i >= 0 && i <= typechars.len(),
    ensures filtered@ == filter_chars_in_typeset(typechars.subrange(0, i), typeset)
{
}

proof fn lemma_min_precedence_char_properties(chars: Seq<char>)
    requires chars.len() > 0,
    ensures chars.contains(min_precedence_char(chars)) &&
        (forall |c: char| chars.contains(c) ==> typechar_precedence(min_precedence_char(chars)) <= typechar_precedence(c))
{
    if chars.len() == 1 {
        assert(chars[0] == min_precedence_char(chars));
        assert(forall |c: char| chars.contains(c) ==> typechar_precedence(chars[0]) <= typechar_precedence(c));
    } else {
        let first = chars[0];
        let rest = chars.skip(1);
        lemma_min_precedence_char_properties(rest);
        let rest_min = min_precedence_char(rest);
        if typechar_precedence(first) <= typechar_precedence(rest_min) {
            assert(min_precedence_char(chars) == first);
            assert(forall |c: char| rest.contains(c) ==> typechar_precedence(first) <= typechar_precedence(c));
            assert(forall |c: char| chars.contains(c) ==> typechar_precedence(first) <= typechar_precedence(c));
        } else {
            assert(min_precedence_char(chars) == rest_min);
            assert(forall |c: char| chars.contains(c) ==> typechar_precedence(rest_min) <= typechar_precedence(c));
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
/* code modified by LLM (iteration 5): Simplified loop invariants to avoid subrange syntax issues */
{
    let mut filtered = Vec::new();
    let mut i = 0;
    while i < typechars.len()
        invariant i <= typechars.len()
    {
        let c = typechars[i];
        if typeset.contains(&c) {
            filtered.push(c);
        }
        i += 1;
    }
    
    proof {
        if filtered.len() > 0 {
            lemma_min_precedence_char_properties(filtered@);
        }
    }
    
    if filtered.is_empty() {
        default
    } else {
        let mut min_char = filtered[0];
        let mut j = 1;
        while j < filtered.len()
            invariant j <= filtered.len(),
            invariant filtered@.contains(min_char),
            invariant forall |k: int| 0 <= k && k < j ==> typechar_precedence(min_char) <= typechar_precedence(filtered@[k])
        {
            let current = filtered[j];
            if typechar_precedence(current) < typechar_precedence(min_char) {
                min_char = current;
            }
            j += 1;
        }
        
        if filtered.contains(&'F') && filtered.contains(&'d') {
            'D'
        } else {
            min_char
        }
    }
}
// </vc-code>

}
fn main() {}