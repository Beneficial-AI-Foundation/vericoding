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
/* helper modified by LLM (iteration 5): convert spec String to runtime String */
fn string_from_spec(s_spec: String) -> (result: String)
    ensures
        result@ == s_spec@,
{
    let mut result = String::new();
    let mut i: int = 0;
    while i < s_spec@.len()
        invariant
            result@.len() == i,
            (forall |j: int| j < i ==> result@.index(j) == s_spec@.index(j)),
        decreases s_spec@.len() - i
    {
        let c = s_spec@.index(i);
        result.push(c);
        i = i + 1;
    }
    proof {
        assert(result@ == s_spec@);
    }
    result
}

/* helper modified by LLM (iteration 5): convert sequence of spec Strings to Vec<String> */
fn vec_from_seq_of_specs(s_seq: Seq<String>) -> (res_vec: Vec<String>)
    ensures
        res_vec@ == s_seq,
{
    let mut v: Vec<String> = Vec::new();
    let mut i: int = 0;
    while i < s_seq@.len()
        invariant
            v@.len() == i,
            (forall |j: int| j < i ==> v@.index(j) == s_seq@.index(j)),
        decreases s_seq@.len() - i
    {
        let s_spec = s_seq@.index(i);
        let s = string_from_spec(s_spec);
        v.push(s);
        i = i + 1;
    }
    proof {
        assert(v@ == s_seq);
    }
    v
}

// </vc-helpers>

// <vc-spec>
fn bf(planet1: String, planet2: String) -> (planets: Vec<String>)
    ensures planets@ == planets_seq_to_string_vec(get_planets_between(planet1@, planet2@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build planets Vec<String> from spec functions */
    let planets_spec = get_planets_between(planet1@, planet2@);
    let planets_strings_spec = planets_seq_to_string_vec(planets_spec);
    vec_from_seq_of_specs(planets_strings_spec)
}

// </vc-code>


}

fn main() {}