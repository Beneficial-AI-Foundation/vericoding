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
/* helper modified by LLM (iteration 5): runtime and vector helper functions and proofs */
fn vec_contains(v: &Vec<char>, target: char) -> bool {
    let mut i: usize = 0;
    while i < v.len() {
        invariant(i <= v.len());
        decreases(v.len() - i);
        if v[i] == target {
            return true;
        }
        i += 1;
    }
    false
}

fn runtime_precedence(c: char) -> nat {
    match c {
        'g' => 0usize,
        'd' => 1usize,
        'f' => 2usize,
        'F' => 3usize,
        'D' => 4usize,
        'G' => 5usize,
        _ => 6usize,
    }
}

fn min_precedence_in_vec(v: &Vec<char>) -> char {
    if v.len() == 0 {
        'G'
    } else {
        let mut best = v[0];
        let mut i: usize = 1;
        while i < v.len() {
            invariant(i <= v.len());
            decreases(v.len() - i);
            let c = v[i];
            if runtime_precedence(c) < runtime_precedence(best) {
                best = c;
            }
            i += 1;
        }
        best
    }
}

spec fn choose_mintype_seq(intersection: Seq<char>, default: char) -> char {
    if intersection.len() == 0 {
        default
    } else if intersection.contains('F') && intersection.contains('d') {
        'D'
    } else {
        min_precedence_char(intersection)
    }
}

fn choose_mintype_vec(intersection: &Vec<char>, default: char) -> char {
    if intersection.len() == 0 {
        default
    } else if vec_contains(intersection, 'F') && vec_contains(intersection, 'd') {
        'D'
    } else {
        min_precedence_in_vec(intersection)
    }
}

proof fn runtime_matches_spec(c: char) ensures runtime_precedence(c) == typechar_precedence(c) {
    match c {
        'g' => { assert(runtime_precedence('g') == typechar_precedence('g')); }
        'd' => { assert(runtime_precedence('d') == typechar_precedence('d')); }
        'f' => { assert(runtime_precedence('f') == typechar_precedence('f')); }
        'F' => { assert(runtime_precedence('F') == typechar_precedence('F')); }
        'D' => { assert(runtime_precedence('D') == typechar_precedence('D')); }
        'G' => { assert(runtime_precedence('G') == typechar_precedence('G')); }
        _   => { assert(runtime_precedence(c) == typechar_precedence(c)); }
    }
}

proof fn min_precedence_in_vec_matches_spec(v: &Vec<char>) ensures min_precedence_in_vec(v) == min_precedence_char(v@) decreases v.len() {
    if v.len() == 0 {
        assert(min_precedence_in_vec(v) == 'G');
        assert(min_precedence_char(v@) == 'G');
    } else if v.len() == 1 {
        assert(min_precedence_in_vec(v) == v[0]);
        assert(min_precedence_char(v@) == v[0]);
    } else {
        let first = v[0];
        let mut rest: Vec<char> = Vec::new();
        let mut i: usize = 1;
        while i < v.len() {
            invariant(i <= v.len());
            decreases(v.len() - i);
            rest.push(v[i]);
            i += 1;
        }
        min_precedence_in_vec_matches_spec(&rest);
        let rest_min = min_precedence_in_vec(&rest);
        runtime_matches_spec(first);
        runtime_matches_spec(rest_min);
        if runtime_precedence(first) <= runtime_precedence(rest_min) {
            assert(min_precedence_in_vec(v) == first);
            assert(min_precedence_char(v@) == first);
        } else {
            assert(min_precedence_in_vec(v) == rest_min);
            assert(min_precedence_char(v@) == rest_min);
        }
    }
}

proof fn choose_mintype_vec_matches_spec(v: &Vec<char>, default: char) ensures choose_mintype_vec(v, default) == choose_mintype_seq(v@, default) decreases v.len() {
    if v.len() == 0 {
        assert(choose_mintype_vec(v, default) == default);
        assert(choose_mintype_seq(v@, default) == default);
    } else {
        if vec_contains(v, 'F') && vec_contains(v, 'd') {
            assert(choose_mintype_vec(v, default) == 'D');
            assert(choose_mintype_seq(v@, default) == 'D');
        } else {
            min_precedence_in_vec_matches_spec(v);
            assert(choose_mintype_vec(v, default) == min_precedence_in_vec(v));
            assert(choose_mintype_seq(v@, default) == min_precedence_char(v@));
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
    /* code modified by LLM (iteration 5): compute intersection of typechars with typeset and choose mintype via helper */
    let mut intersection: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < typechars.len() {
        invariant(i <= typechars.len());
        decreases(typechars.len() - i);
        let c = typechars[i];
        if vec_contains(&typeset, c) {
            intersection.push(c);
        }
        i += 1;
    }
    choose_mintype_vec(&intersection, default)
}
// </vc-code>

}
fn main() {}