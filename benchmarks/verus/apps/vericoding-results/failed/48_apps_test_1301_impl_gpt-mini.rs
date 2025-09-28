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
/* helper modified by LLM (iteration 5): convert Seq<char> to Vec<char> using int indexing */
fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    ensures
        v@ == s,
{
    let mut v: Vec<char> = Vec::new();
    let mut k: int = 0;
    while k < s.len()
        invariant
            k <= s.len(),
            v@.len() == k,
        decreases s.len() - k
    {
        let c: char = s.index(k);
        v.push(c);
        k = k + 1;
    }
    v
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
/* code modified by LLM (iteration 5): iterate pokemon list and return first matching name */
{
    let list = get_pokemon_list();
    let mut i: int = 0;
    while i < list.len()
        invariant
            i <= list.len(),
            forall|j: int| j < i ==> (list.index(j).len() != input@.len() || !matches_pattern(list.index(j), input@)),
        decreases list.len() - i
    {
        let candidate: Seq<char> = list.index(i);
        if candidate.len() == input@.len() && matches_pattern(candidate, input@) {
            return seq_to_vec(candidate);
        }
        i = i + 1;
    }
    seq_to_vec(get_pokemon_list().index(0))
}

// </vc-code>


}

fn main() {}