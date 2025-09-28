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
/* helper modified by LLM (iteration 5): remove noop-helpers */
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
/* code modified by LLM (iteration 5): Fixed type issues with `nat` and `int` casts. */
{
    let input_seq = input@;
    let pokemon_list: Seq<Seq<char>> = get_pokemon_list();

    let mut result: Option<Seq<char>> = Option::None;
    let mut i: int = 0; // Changed to int for loop condition

    while i < pokemon_list.len()
        invariant
            0 <= i && i <= pokemon_list.len(),
            result.is_None() || 
                (result.is_Some() && 
                matches_pattern(result.get_Some_0(), input_seq) &&
                result.get_Some_0().len() == input_seq.len()),
            forall |k: int| 0 <= k < i && pokemon_list[k].len() == input_seq.len() && matches_pattern(pokemon_list[k], input_seq) ==> 
                result.is_Some() && (exists |j: int| 0 <= j < pokemon_list.len() && pokemon_list[j] == result.get_Some_0()),
        decreases pokemon_list.len() - i
    {
        let current_pokemon_name = pokemon_list.index(i);

        if current_pokemon_name.len() == input_seq.len() && matches_pattern(current_pokemon_name, input_seq) {
            if result.is_None() {
                result = Option::Some(current_pokemon_name);
            }
        }
        i = i + 1;
    }

    let final_result_seq = result.unwrap();

    proof {
        assert(is_first_match(final_result_seq, input_seq, pokemon_list));
        assert(valid_pokemon_name(final_result_seq));
        assert(exists|idx: int| 0 <= idx < pokemon_list.len() && pokemon_list[idx] == final_result_seq && matches_pattern(final_result_seq, input_seq));
    }
    Vec::new(final_result_seq)
}
// </vc-code>


}

fn main() {}