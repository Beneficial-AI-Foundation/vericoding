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
fn matches_pattern_exec(pokemon_name: &Vec<char>, pattern: &Vec<char>) -> (result: bool)
    requires
        pokemon_name.len() == pattern.len(),
    ensures
        result == matches_pattern(pokemon_name@, pattern@),
{
    let mut i = 0;
    while i < pattern.len()
        invariant
            pokemon_name.len() == pattern.len(),
            0 <= i <= pattern.len(),
            forall|j: int| 0 <= j < i ==> (pattern@[j] == '.' || pattern@[j] == pokemon_name@[j]),
    {
        if pattern[i] != '.' && pattern[i] != pokemon_name[i] {
            return false;
        }
        i = i + 1;
    }
    true
}

/* helper modified by LLM (iteration 2): fixed lifetime specifiers for POKEMON_LIST to resolve compilation error */
const POKEMON_LIST: &'static [&'static [char]] = &[
    &['v','a','p','o','r','e','o','n'],
    &['j','o','l','t','e','o','n'],
    &['f','l','a','r','e','o','n'],
    &['e','s','p','e','o','n'],
    &['u','m','b','r','e','o','n'],
    &['l','e','a','f','e','o','n'],
    &['g','l','a','c','e','o','n'],
    &['s','y','l','v','e','o','n'],
];

proof fn lemma_pokemon_list_correspondence()
    ensures
        POKEMON_LIST@.len() == get_pokemon_list().len(),
        forall|i: int| 0 <= i < POKEMON_LIST@.len() ==> POKEMON_LIST@[i]@ == get_pokemon_list()[i],
{}

/* helper modified by LLM (iteration 5): changed axiomatic lemma to a proof */
proof fn lemma_get_pokemon_list_ensures_valid()
    ensures
        forall|i: int| 0 <= i < get_pokemon_list().len() ==> valid_pokemon_name(get_pokemon_list()[i]),
{
    assert(valid_pokemon_name(get_pokemon_list()[0]));
    assert(valid_pokemon_name(get_pokemon_list()[1]));
    assert(valid_pokemon_name(get_pokemon_list()[2]));
    assert(valid_pokemon_name(get_pokemon_list()[3]));
    assert(valid_pokemon_name(get_pokemon_list()[4]));
    assert(valid_pokemon_name(get_pokemon_list()[5]));
    assert(valid_pokemon_name(get_pokemon_list()[6]));
    assert(valid_pokemon_name(get_pokemon_list()[7]));
}

/* helper modified by LLM (iteration 4): simplified implementation of lemma_pokemon_in_list_is_valid */
proof fn lemma_pokemon_in_list_is_valid(pokemon_name: Seq<char>)
    requires
        exists|i: int| 0 <= i < get_pokemon_list().len() && get_pokemon_list()[i] == pokemon_name,
    ensures
        valid_pokemon_name(pokemon_name),
{
    lemma_get_pokemon_list_ensures_valid();
    let i = choose|i: int| 0 <= i < get_pokemon_list().len() && get_pokemon_list()[i] == pokemon_name;
    assert(valid_pokemon_name(get_pokemon_list()[i]));
    assert(valid_pokemon_name(pokemon_name));
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
    /* code modified by LLM (iteration 5): fixed mismatched types compile error by using unreached() */
    lemma_pokemon_list_correspondence();

    let mut i: usize = 0;
    while i < POKEMON_LIST.len()
        invariant
            0 <= i <= POKEMON_LIST.len(),
            POKEMON_LIST@.len() == get_pokemon_list().len(),
            forall|k: int| 0 <= k < POKEMON_LIST@.len() ==> POKEMON_LIST@[k]@ == get_pokemon_list()[k],
            forall|j: int| 0 <= j < i ==> (
                get_pokemon_list()[j].len() != input@.len() ||
                !matches_pattern(get_pokemon_list()[j], input@)
            ),
    {
        let pokemon_name_slice = POKEMON_LIST[i];
        let pokemon_name_vec = pokemon_name_slice.to_vec();

        if pokemon_name_vec.len() == input.len() {
            if matches_pattern_exec(&pokemon_name_vec, &input) {
                proof {
                    let result_seq = pokemon_name_vec@;
                    assert(exists|k: int| 0 <= k < get_pokemon_list().len() && get_pokemon_list()[k] == result_seq);
                    lemma_pokemon_in_list_is_valid(result_seq);
                    assert(is_first_match(result_seq, input@, get_pokemon_list()));
                }
                return pokemon_name_vec;
            }
        }
        i = i + 1;
    }

    unreached();
}
// </vc-code>


}

fn main() {}