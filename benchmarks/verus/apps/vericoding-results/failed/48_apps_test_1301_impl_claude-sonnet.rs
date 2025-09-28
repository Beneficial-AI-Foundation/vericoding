// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_pokemon_name(name: Seq<char>) -> bool {
    name == seq!['v','a','p','o','r','e','o','n'] || 
    name == seq!['j','o','l','t','e','o','n'] || 
    name == seq!['f','l','a','r','e','o','n'] || 
    name == seq!['e','s','p','e','o','n'] ||
    name == seq!['u','m','b','r','e','o','n'] || 
    name == seq!['l','e','a','f','e','o','n'] || 
    name == seq!['g','l','a','c','e','o','n'] || 
    name == seq!['s','y','l','v','e','o','n']
}

spec fn matches_pattern(pokemon_name: Seq<char>, pattern: Seq<char>) -> bool
    recommends pokemon_name.len() == pattern.len()
{
    pokemon_name.len() == pattern.len() &&
    forall|i: int| 0 <= i < pattern.len() ==> (pattern[i] == '.' || pattern[i] == pokemon_name[i])
}

spec fn get_pokemon_list() -> Seq<Seq<char>> {
    seq![
        seq!['v','a','p','o','r','e','o','n'],
        seq!['j','o','l','t','e','o','n'],
        seq!['f','l','a','r','e','o','n'],
        seq!['e','s','p','e','o','n'],
        seq!['u','m','b','r','e','o','n'],
        seq!['l','e','a','f','e','o','n'],
        seq!['g','l','a','c','e','o','n'],
        seq!['s','y','l','v','e','o','n']
    ]
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
    /* Additional validation logic would be implemented here */
}

spec fn is_first_match(result: Seq<char>, pattern: Seq<char>, pokemon_list: Seq<Seq<char>>) -> bool {
    exists|i: int| 0 <= i < pokemon_list.len() && 
        pokemon_list[i] == result &&
        result.len() == pattern.len() &&
        matches_pattern(result, pattern) &&
        forall|j: int| 0 <= j < i ==> (pokemon_list[j].len() != pattern.len() || !matches_pattern(pokemon_list[j], pattern))
}
// </vc-preamble>

// <vc-helpers>
exec fn char_matches(pokemon_char: char, pattern_char: char) -> (result: bool)
    ensures
        result == (pattern_char == '.' || pattern_char == pokemon_char),
{
    pattern_char == '.' || pattern_char == pokemon_char
}

exec fn check_pattern_match(pokemon: &Vec<char>, pattern: &Vec<char>) -> (result: bool)
    requires
        pokemon.len() == pattern.len(),
    ensures
        result == matches_pattern(pokemon@, pattern@),
{
    if pokemon.len() != pattern.len() {
        return false;
    }
    
    let mut i = 0;
    while i < pokemon.len()
        invariant
            0 <= i <= pokemon.len(),
            pokemon.len() == pattern.len(),
            forall|j: int| 0 <= j < i ==> (pattern@[j] == '.' || pattern@[j] == pokemon@[j]),
    {
        if !char_matches(pokemon[i], pattern[i]) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires
        valid_input(input@),
    ensures
        valid_pokemon_name(result@),
        is_first_match(result@, input@, get_pokemon_list()),
        exists|i: int| 0 <= i < get_pokemon_list().len() && 
            get_pokemon_list()[i] == result@ &&
            matches_pattern(result@, input@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed matches_pattern call to pass input@ as pattern argument */
    let pokemon_list = vec![
        vec!['v','a','p','o','r','e','o','n'],
        vec!['j','o','l','t','e','o','n'],
        vec!['f','l','a','r','e','o','n'],
        vec!['e','s','p','e','o','n'],
        vec!['u','m','b','r','e','o','n'],
        vec!['l','e','a','f','e','o','n'],
        vec!['g','l','a','c','e','o','n'],
        vec!['s','y','l','v','e','o','n']
    ];
    
    let mut i = 0;
    while i < pokemon_list.len()
        invariant
            0 <= i <= pokemon_list.len(),
            pokemon_list@ == get_pokemon_list(),
            forall|j: int| 0 <= j < i ==> (pokemon_list@[j].len() != input@.len() || !matches_pattern(pokemon_list@[j], input@)),
    {
        let pokemon = &pokemon_list[i];
        if pokemon.len() == input.len() {
            if check_pattern_match(pokemon, &input) {
                return pokemon.clone();
            }
        }
        i += 1;
    }
    
    vec!['v','a','p','o','r','e','o','n']
}
// </vc-code>


}

fn main() {}