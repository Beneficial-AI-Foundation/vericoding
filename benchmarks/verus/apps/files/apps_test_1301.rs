// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {

spec fn valid_pokemon_name(name: Seq<char>) -> bool {
    name == seq!['v', 'a', 'p', 'o', 'r', 'e', 'o', 'n'] || 
    name == seq!['j', 'o', 'l', 't', 'e', 'o', 'n'] || 
    name == seq!['f', 'l', 'a', 'r', 'e', 'o', 'n'] || 
    name == seq!['e', 's', 'p', 'e', 'o', 'n'] ||
    name == seq!['u', 'm', 'b', 'r', 'e', 'o', 'n'] || 
    name == seq!['l', 'e', 'a', 'f', 'e', 'o', 'n'] || 
    name == seq!['g', 'l', 'a', 'c', 'e', 'o', 'n'] || 
    name == seq!['s', 'y', 'l', 'v', 'e', 'o', 'n']
}

spec fn matches_pattern(pokemon_name: Seq<char>, pattern: Seq<char>) -> bool
    recommends pokemon_name.len() == pattern.len()
{
    forall|i: int| 0 <= i < pattern.len() ==> (pattern[i] == '.' || pattern[i] == pokemon_name[i])
}

spec fn get_pokemon_list() -> Seq<Seq<char>> {
    seq![
        seq!['v', 'a', 'p', 'o', 'r', 'e', 'o', 'n'],
        seq!['j', 'o', 'l', 't', 'e', 'o', 'n'],
        seq!['f', 'l', 'a', 'r', 'e', 'o', 'n'],
        seq!['e', 's', 'p', 'e', 'o', 'n'],
        seq!['u', 'm', 'b', 'r', 'e', 'o', 'n'],
        seq!['l', 'e', 'a', 'f', 'e', 'o', 'n'],
        seq!['g', 'l', 'a', 'c', 'e', 'o', 'n'],
        seq!['s', 'y', 'l', 'v', 'e', 'o', 'n']
    ]
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && 
    ({
        let lines = split_lines(input);
        lines.len() >= 2 &&
        (lines[0].len() > 0 && forall|i: int| 0 <= i < lines[0].len() ==> '0' <= lines[0][i] <= '9') &&
        6 <= lines[1].len() <= 8 &&
        forall|i: int| 0 <= i < lines[1].len() ==> ('a' <= lines[1][i] <= 'z' || lines[1][i] == '.') &&
        exists|j: int| 0 <= j < get_pokemon_list().len() && get_pokemon_list()[j].len() == lines[1].len() && matches_pattern(get_pokemon_list()[j], lines[1])
    })
}

spec fn is_first_match(result: Seq<char>, pattern: Seq<char>, pokemon_list: Seq<Seq<char>>) -> bool {
    exists|i: int| 0 <= i < pokemon_list.len() && 
        pokemon_list[i] == result &&
        result.len() == pattern.len() &&
        matches_pattern(result, pattern) &&
        forall|j: int| 0 <= j < i ==> (pokemon_list[j].len() != pattern.len() || !matches_pattern(pokemon_list[j], pattern))
}

#[verifier::external_body]
spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires valid_input(input@)
    ensures 
        valid_pokemon_name(result@)
        && {
            let lines = split_lines(input@);
            is_first_match(result@, lines[1], get_pokemon_list())
        }
        && {
            let lines = split_lines(input@);
            exists|i: int| 0 <= i < get_pokemon_list().len() && 
                get_pokemon_list()[i] == result@ &&
                result@.len() == lines[1].len() &&
                matches_pattern(result@, lines[1])
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}