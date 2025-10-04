// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn string_lex_ge(s1: Seq<char>, s2: Seq<char>) -> bool
    decreases s1.len()
{
    if s1.len() == 0 && s2.len() == 0 {
        true
    } else if s1.len() == 0 {
        false
    } else if s2.len() == 0 {
        true
    } else if s1[0] > s2[0] {
        true
    } else if s1[0] < s2[0] {
        false
    } else {
        string_lex_ge(s1.skip(1), s2.skip(1))
    }
}

spec fn string_lex_le(s1: Seq<char>, s2: Seq<char>) -> bool
    decreases s1.len()
{
    if s1.len() == 0 && s2.len() == 0 {
        true
    } else if s1.len() == 0 {
        true
    } else if s2.len() == 0 {
        false
    } else if s1[0] < s2[0] {
        true
    } else if s1[0] > s2[0] {
        false
    } else {
        string_lex_le(s1.skip(1), s2.skip(1))
    }
}

spec fn has_substring_at(s: Seq<char>, pattern: Seq<char>, pos: int) -> bool
{
    pos >= 0 && pos + pattern.len() <= s.len() &&
    s.subrange(pos, pos + pattern.len()) == pattern
}

spec fn contains_substring(s: Seq<char>, pattern: Seq<char>) -> bool
{
    pattern.len() > 0 && 
    (exists|pos: int| #[trigger] has_substring_at(s, pattern, pos))
}

fn failure(pattern: &Vec<char>) -> (result: Vec<usize>)
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}

fn find_good_strings(n: usize, s1: &Vec<char>, s2: &Vec<char>, evil: &Vec<char>) -> (result: usize)
    requires 
        n > 0,
        s1.len() == n,
        s2.len() == n,
        evil.len() > 0,
        string_lex_le(s1@, s2@),
    ensures 
        result < 1000000007
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {
    /*
    let s1 = vec!['a', 'a'];
    let s2 = vec!['d', 'a'];
    let evil = vec!['b'];
    println!("{}", find_good_strings(2, &s1, &s2, &evil));
    
    let s1 = vec!['l', 'e', 'e', 't', 'c', 'o', 'd', 'e'];
    let s2 = vec!['l', 'e', 'e', 't', 'g', 'o', 'e', 's'];
    let evil = vec!['l', 'e', 'e', 't'];
    println!("{}", find_good_strings(8, &s1, &s2, &evil));
    
    let s1 = vec!['g', 'x'];
    let s2 = vec!['g', 'z'];
    let evil = vec!['x'];
    println!("{}", find_good_strings(2, &s1, &s2, &evil));
    */
}