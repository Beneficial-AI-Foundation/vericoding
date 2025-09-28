// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() == 1 && 'a' <= input[0] && input[0] <= 'z'
}

spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

spec fn expected_output(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    if is_vowel(input[0]) { seq!['v', 'o', 'w', 'e', 'l'] } else { seq!['c', 'o', 'n', 's', 'o', 'n', 'a', 'n', 't'] }
}
// </vc-preamble>

// <vc-helpers>
fn is_vowel_exec(c: char) -> (b: bool)
    ensures
        b == is_vowel(c),
{
    let r = c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u';
    r
}

fn build_vowel_vec() -> (v: Vec<char>)
    ensures
        v@ == seq!['v', 'o', 'w', 'e', 'l'],
{
    let mut out: Vec<char> = Vec::new();
    out.push('v');
    out.push('o');
    out.push('w');
    out.push('e');
    out.push('l');
    out
}

fn build_consonant_vec() -> (v: Vec<char>)
    ensures
        v@ == seq!['c', 'o', 'n', 's', 'o', 'n', 'a', 'n', 't'],
{
    let mut out: Vec<char> = Vec::new();
    out.push('c');
    out.push('o');
    out.push('n');
    out.push('s');
    out.push('o');
    out.push('n');
    out.push('a');
    out.push('n');
    out.push('t');
    out
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(input@),
    ensures 
        result@ == expected_output(input@),
        result@ == seq!['v', 'o', 'w', 'e', 'l'] || result@ == seq!['c', 'o', 'n', 's', 'o', 'n', 'a', 'n', 't'],
// </vc-spec>
// <vc-code>
{
    assert(input@.len() == 1);
    assert(0 < input.len());
    let c = input[0];
    assert(c == input@[0]);

    let b = is_vowel_exec(c);
    if b {
        let v = build_vowel_vec();
        proof {
            assert(is_vowel(c));
            assert(is_vowel(input@[0]));
            assert(expected_output(input@) == seq!['v', 'o', 'w', 'e', 'l']);
        }
        v
    } else {
        let v = build_consonant_vec();
        proof {
            assert(!is_vowel(c));
            assert(!is_vowel(input@[0]));
            assert(expected_output(input@) == seq!['c', 'o', 'n', 's', 'o', 'n', 'a', 'n', 't']);
        }
        v
    }
}
// </vc-code>


}

fn main() {}