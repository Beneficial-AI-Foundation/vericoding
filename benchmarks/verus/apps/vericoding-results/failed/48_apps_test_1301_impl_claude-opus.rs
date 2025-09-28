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
    /* code modified by LLM (iteration 5): fixed type mismatch by using @ view for both args to matches_pattern */
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
    
    let mut i: usize = 0;
    let mut result = vec![];
    
    while i < pokemon_list.len()
        invariant
            0 <= i <= pokemon_list.len(),
            pokemon_list.len() == 8,
            pokemon_list@[0] == seq!['v','a','p','o','r','e','o','n'],
            pokemon_list@[1] == seq!['j','o','l','t','e','o','n'],
            pokemon_list@[2] == seq!['f','l','a','r','e','o','n'],
            pokemon_list@[3] == seq!['e','s','p','e','o','n'],
            pokemon_list@[4] == seq!['u','m','b','r','e','o','n'],
            pokemon_list@[5] == seq!['l','e','a','f','e','o','n'],
            pokemon_list@[6] == seq!['g','l','a','c','e','o','n'],
            pokemon_list@[7] == seq!['s','y','l','v','e','o','n'],
            forall|k: int| 0 <= k < 8 ==> pokemon_list@[k] == get_pokemon_list()[k],
            forall|j: int| 0 <= j < i as int ==> (pokemon_list@[j].len() != input@.len() || !matches_pattern(pokemon_list@[j], input@)),
    {
        if pokemon_list[i].len() == input.len() {
            let mut matches = true;
            let mut j: usize = 0;
            
            while j < input.len()
                invariant
                    0 <= j <= input.len(),
                    pokemon_list@[i as int].len() == input@.len(),
                    matches == forall|k: int| 0 <= k < j as int ==> (input@[k] == '.' || input@[k] == pokemon_list@[i as int][k]),
            {
                if input[j] != '.' && input[j] != pokemon_list[i][j] {
                    matches = false;
                }
                j = j + 1;
            }
            
            if matches {
                assert(matches_pattern(pokemon_list@[i as int], input@));
                result = pokemon_list[i].clone();
                assert(valid_pokemon_name(result@));
                assert(is_first_match(result@, input@, get_pokemon_list()));
                return result;
            }
        }
        i = i + 1;
    }
    
    unreached()
}
// </vc-code>


}

fn main() {}