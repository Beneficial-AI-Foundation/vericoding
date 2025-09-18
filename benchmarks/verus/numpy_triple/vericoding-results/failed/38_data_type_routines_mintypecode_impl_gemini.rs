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
/* helper modified by LLM (iteration 4): no changes, just updating comment */
proof fn lemma_filter_singleton_char(c: char, typeset: Seq<char>)
    ensures (seq![c]).filter(|ch: char| char_in_typeset(ch, typeset)) ==
                if char_in_typeset(c, typeset) { seq![c] } else { Seq::<char>::empty() }
{
}

/* helper modified by LLM (iteration 4): no changes, just updating comment */
proof fn lemma_filter_distributes_over_add<A>(s1: Seq<A>, s2: Seq<A>, p: spec_fn(A) -> bool)
    ensures (s1 + s2).filter(p) == s1.filter(p) + s2.filter(p),
    decreases s1.len(),
{
    if s1.len() > 0 {
        lemma_filter_distributes_over_add(s1.drop_last(), s2, p);
    }
}

/* helper modified by LLM (iteration 5): added exec version of typechar_precedence to fix compilation error */
fn typechar_precedence_exec(c: char) -> (res: u64)
    ensures res as nat == typechar_precedence(c),
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
    /* code modified by LLM (iteration 5): called exec version of typechar_precedence to fix compilation error */
    let mut intersection: Vec<char> = Vec::new();
    let mut i = 0;
    while i < typechars.len()
        invariant
            i <= typechars.len(),
            intersection@ == filter_chars_in_typeset(typechars@.subrange(0, i as int), typeset@),
    {
        let c = typechars[i];
        let mut in_typeset = false;
        let mut j = 0;
        while j < typeset.len()
            invariant
                j <= typeset.len(),
                in_typeset <==> typeset@.subrange(0, j as int).contains(c),
        {
            if c == typeset[j] {
                in_typeset = true;
            }
            j = j + 1;
        }

        proof {
            let p = |ch: char| char_in_typeset(ch, typeset@);
            lemma_filter_distributes_over_add(typechars@.subrange(0, i as int), seq![c], p);
            lemma_filter_singleton_char(c, typeset@);
        }

        if in_typeset {
            intersection.push(c);
        }
        i = i + 1;
    }

    if intersection.len() == 0 {
        return default;
    }

    let mut has_F = false;
    let mut has_d = false;
    let mut k = 0;
    while k < intersection.len()
        invariant
            k <= intersection.len(),
            has_F <==> intersection@.subrange(0, k as int).contains('F'),
            has_d <==> intersection@.subrange(0, k as int).contains('d'),
    {
        if intersection[k] == 'F' {
            has_F = true;
        }
        if intersection[k] == 'd' {
            has_d = true;
        }
        k = k + 1;
    }
    
    if has_F && has_d {
        return 'D';
    }

    let mut min_c = intersection[0];
    let mut m = 1;
    while m < intersection.len()
        invariant
            m <= intersection.len(),
            intersection@.len() > 0,
            intersection@.subrange(0, m as int).contains(min_c),
            forall|x: char| intersection@.subrange(0, m as int).contains(x) ==> typechar_precedence(min_c) <= typechar_precedence(x),
    {
        let current_c = intersection[m];
        if typechar_precedence_exec(current_c) < typechar_precedence_exec(min_c) {
            min_c = current_c;
        }
        m = m + 1;
    }
    
    min_c
}
// </vc-code>

}
fn main() {}