// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(stdin_input: Seq<char>, n: int) -> bool {
    exists|lines: Seq<Seq<char>>| (parse_input(stdin_input) == lines &&
    lines.len() >= 1 &&
    lines.len() == n + 1 &&
    parse_int(lines[0]) == n &&
    n >= 1 && n <= 100 &&
    (forall|i: int| 1 <= i < lines.len() ==> 
        1 <= lines[i].len() <= 100 && 
        forall|j: int| 0 <= j < lines[i].len() ==> 'a' <= lines[i][j] <= 'z'))
}

spec fn valid_alphabet_ordering(stdin_input: Seq<char>, alphabet: Seq<char>) -> bool
    recommends alphabet.len() == 26,
              forall|i: int| 0 <= i < alphabet.len() ==> 'a' <= alphabet[i] <= 'z',
              forall|i: int, j: int| 0 <= i < j < alphabet.len() ==> alphabet[i] != alphabet[j]
{
    exists|lines: Seq<Seq<char>>, n: int| (parse_input(stdin_input) == lines &&
    lines.len() >= 1 &&
    lines.len() == n + 1 &&
    parse_int(lines[0]) == n &&
    (forall|i: int| 1 <= i < n ==> lexicographically_less_or_equal(lines[i], lines[i+1], alphabet)))
}

spec fn lexicographically_less_or_equal(s1: Seq<char>, s2: Seq<char>, alphabet: Seq<char>) -> bool
    recommends alphabet.len() == 26,
              forall|i: int| 0 <= i < alphabet.len() ==> 'a' <= alphabet[i] <= 'z',
              forall|i: int, j: int| 0 <= i < j < alphabet.len() ==> alphabet[i] != alphabet[j]
{
    if s1 == s2 {
        true
    } else if s1.len() <= s2.len() && s1 == s2.subrange(0, s1.len() as int) {
        true
    } else if s2.len() < s1.len() && s2 == s1.subrange(0, s2.len() as int) {
        false
    } else {
        exists|i: int| (0 <= i < s1.len() && i < s2.len() && s1[i] != s2[i] &&
        (forall|j: int| 0 <= j < i ==> s1[j] == s2[j]) &&
        'a' <= s1[i] <= 'z' && 'a' <= s2[i] <= 'z' &&
        alphabet_order(s1[i], s2[i], alphabet))
    }
}

spec fn alphabet_order(c1: char, c2: char, alphabet: Seq<char>) -> bool
    recommends alphabet.len() == 26,
              forall|i: int| 0 <= i < alphabet.len() ==> 'a' <= alphabet[i] <= 'z',
              forall|i: int, j: int| 0 <= i < j < alphabet.len() ==> alphabet[i] != alphabet[j],
              'a' <= c1 <= 'z' && 'a' <= c2 <= 'z'
{
    exists|i: int, j: int| 0 <= i < j < alphabet.len() && alphabet[i] == c1 && alphabet[j] == c2
}

spec fn parse_input(input: Seq<char>) -> Seq<Seq<char>>
{
    Seq::<Seq<char>>::empty()
}

spec fn parse_int(s: Seq<char>) -> int
{
    0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: String)
    requires
        stdin_input@.len() > 0,
        exists|n: int| n >= 1 && valid_input(stdin_input@, n),
    ensures
        result@ == "Impossible"@ || (result@.len() == 26 && forall|i: int| 0 <= i < result@.len() ==> 'a' <= result@[i] <= 'z'),
        result@ != "Impossible"@ ==> (forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] != result@[j]),
        result@ != "Impossible"@ ==> valid_alphabet_ordering(stdin_input@, result@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "Impossible".to_string()
    // impl-end
}
// </vc-code>


}

fn main() {}