// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy)]
enum Planet {
    Mercury,
    Venus,
    Earth,
    Mars,
    Jupiter,
    Saturn,
    Uranus,
    Neptune,
}

spec fn planet_from_string(name: Seq<char>) -> Option<Planet> {
    if name == seq!['M','e','r','c','u','r','y'] {
        Some(Planet::Mercury)
    } else if name == seq!['V','e','n','u','s'] {
        Some(Planet::Venus)
    } else if name == seq!['E','a','r','t','h'] {
        Some(Planet::Earth)
    } else if name == seq!['M','a','r','s'] {
        Some(Planet::Mars)
    } else if name == seq!['J','u','p','i','t','e','r'] {
        Some(Planet::Jupiter)
    } else if name == seq!['S','a','t','u','r','n'] {
        Some(Planet::Saturn)
    } else if name == seq!['U','r','a','n','u','s'] {
        Some(Planet::Uranus)
    } else if name == seq!['N','e','p','t','u','n','e'] {
        Some(Planet::Neptune)
    } else {
        None
    }
}

spec fn planet_index(p: Planet) -> int {
    match p {
        Planet::Mercury => 0int,
        Planet::Venus => 1int,
        Planet::Earth => 2int,
        Planet::Mars => 3int,
        Planet::Jupiter => 4int,
        Planet::Saturn => 5int,
        Planet::Uranus => 6int,
        Planet::Neptune => 7int,
    }
}

spec fn get_planets_between(planet1: Seq<char>, planet2: Seq<char>) -> Seq<Seq<char>> {
    let p1 = planet_from_string(planet1);
    let p2 = planet_from_string(planet2);
    if p1.is_none() || p2.is_none() {
        seq![]
    } else {
        let i1 = planet_index(p1.unwrap());
        let i2 = planet_index(p2.unwrap());
        if i1 < i2 {
            get_planets_between_indices(i1 + 1, i2 - 1)
        } else if i1 > i2 {
            get_planets_between_indices(i2 + 1, i1 - 1)
        } else {
            seq![]
        }
    }
}

spec fn get_planets_between_indices(start: int, end: int) -> Seq<Seq<char>>
    recommends 0 <= start <= 7 && 0 <= end <= 7
    decreases if start <= end { end - start + 1 } else { 0 }
{
    if start > end {
        seq![]
    } else {
        if start == 0int {
            seq![seq!['M','e','r','c','u','r','y']].add(get_planets_between_indices(1int, end))
        } else if start == 1int {
            seq![seq!['V','e','n','u','s']].add(get_planets_between_indices(2int, end))
        } else if start == 2int {
            seq![seq!['E','a','r','t','h']].add(get_planets_between_indices(3int, end))
        } else if start == 3int {
            seq![seq!['M','a','r','s']].add(get_planets_between_indices(4int, end))
        } else if start == 4int {
            seq![seq!['J','u','p','i','t','e','r']].add(get_planets_between_indices(5int, end))
        } else if start == 5int {
            seq![seq!['S','a','t','u','r','n']].add(get_planets_between_indices(6int, end))
        } else if start == 6int {
            seq![seq!['U','r','a','n','u','s']].add(get_planets_between_indices(7int, end))
        } else if start == 7int {
            seq![seq!['N','e','p','t','u','n','e']]
        } else {
            seq![]
        }
    }
}

spec fn seq_char_to_string(chars: Seq<char>) -> String {
    arbitrary()
}

spec fn planets_seq_to_string_vec(planets: Seq<Seq<char>>) -> Seq<String> 
    decreases planets.len()
{
    if planets.len() == 0 {
        seq![]
    } else {
        let first_planet = planets[0];
        let rest = planets.drop_first();
        seq![seq_char_to_string(first_planet)].add(planets_seq_to_string_vec(rest))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a helper function to convert a Seq<char> to a String by iteratively pushing chars as u8 bytes to a Vec<u8> and then converting the Vec<u8> to a String. */
pfn seq_char_to_rust_string(s: Seq<char>) -> (result: String)
    ensures
        s.len() == result@.len(),
        forall |i: int| #![auto]
            0 <= i < s.len() ==> s[i] == result@[i]
{
    let mut vec_u8 = Vec::<u8>::new();
    let mut j: nat = 0;
    while j < s.len()
        invariant
            0 <= j <= s.len(),
            vec_u8.len() == j,
            vec_u8@ == s.subsequence(0, j).map(|c: char| c as u8),
        decreases s.len() - j
    {
        vec_u8.push(s[j] as u8);
        j = j + 1;
    }
    String::from_utf8(vec_u8).unwrap()
}
// </vc-helpers>

// <vc-spec>
fn bf(planet1: String, planet2: String) -> (planets: Vec<String>)
    ensures planets@ == planets_seq_to_string_vec(get_planets_between(planet1@, planet2@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [brief description] */
{
    let p1_seq = planet1@;
    let p2_seq = planet2@;

    let opt_p1 = planet_from_string(p1_seq);
    let opt_p2 = planet_from_string(p2_seq);

    if opt_p1.is_none() || opt_p2.is_none() {
        return Vec::new();
    }

    let idx1 = planet_index(opt_p1.unwrap());
    let idx2 = planet_index(opt_p2.unwrap());

    let result_seq: Seq<Seq<char>>;
    if idx1 < idx2 {
        result_seq = get_planets_between_indices(idx1 + 1, idx2 - 1);
    } else if idx1 > idx2 {
        result_seq = get_planets_between_indices(idx2 + 1, idx1 - 1);
    } else {
        result_seq = seq![];
    }

    let mut result_vec: Vec<String> = Vec::new();
    let mut i: nat = 0;

    while i < result_seq.len()
        invariant
            0 <= i <= result_seq.len(),
            result_vec.len() == i,
            result_vec@ == planets_seq_to_string_vec(result_seq.subsequence(0, i)),
        decreases result_seq.len() - i
    {
        let planet_name_seq = result_seq[i];
        let planet_name_string = seq_char_to_rust_string(planet_name_seq);

        result_vec.push(planet_name_string);
        i = i + 1;
    }

    result_vec
}
// </vc-code>


}

fn main() {}