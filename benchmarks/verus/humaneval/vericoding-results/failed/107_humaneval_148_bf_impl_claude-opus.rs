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
/* helper modified by LLM (iteration 5): Fixed indexing to use proper syntax without 'as int' */
fn seq_char_equals(s1: &Seq<char>, s2: &Seq<char>) -> (result: bool)
    ensures result == (*s1 == *s2)
{
    if s1.len() != s2.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i < s1.len() as usize
        invariant
            0 <= i <= s1.len(),
            s1.len() == s2.len(),
            forall|j: int| 0 <= j < i as int ==> s1[j] == s2[j]
    {
        proof {
            assert(i < s1.len());
        }
        if s1@[i] != s2@[i] {
            return false;
        }
        i = i + 1;
    }
    
    true
}
// </vc-helpers>

// <vc-spec>
fn bf(planet1: String, planet2: String) -> (planets: Vec<String>)
    ensures planets@ == planets_seq_to_string_vec(get_planets_between(planet1@, planet2@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed sequence comparison and String creation */
    let p1_chars = planet1@;
    let p2_chars = planet2@;
    
    let p1_opt = if seq_char_equals(&p1_chars, &seq!['M','e','r','c','u','r','y']) {
        Some(Planet::Mercury)
    } else if seq_char_equals(&p1_chars, &seq!['V','e','n','u','s']) {
        Some(Planet::Venus)
    } else if seq_char_equals(&p1_chars, &seq!['E','a','r','t','h']) {
        Some(Planet::Earth)
    } else if seq_char_equals(&p1_chars, &seq!['M','a','r','s']) {
        Some(Planet::Mars)
    } else if seq_char_equals(&p1_chars, &seq!['J','u','p','i','t','e','r']) {
        Some(Planet::Jupiter)
    } else if seq_char_equals(&p1_chars, &seq!['S','a','t','u','r','n']) {
        Some(Planet::Saturn)
    } else if seq_char_equals(&p1_chars, &seq!['U','r','a','n','u','s']) {
        Some(Planet::Uranus)
    } else if seq_char_equals(&p1_chars, &seq!['N','e','p','t','u','n','e']) {
        Some(Planet::Neptune)
    } else {
        None
    };
    
    let p2_opt = if seq_char_equals(&p2_chars, &seq!['M','e','r','c','u','r','y']) {
        Some(Planet::Mercury)
    } else if seq_char_equals(&p2_chars, &seq!['V','e','n','u','s']) {
        Some(Planet::Venus)
    } else if seq_char_equals(&p2_chars, &seq!['E','a','r','t','h']) {
        Some(Planet::Earth)
    } else if seq_char_equals(&p2_chars, &seq!['M','a','r','s']) {
        Some(Planet::Mars)
    } else if seq_char_equals(&p2_chars, &seq!['J','u','p','i','t','e','r']) {
        Some(Planet::Jupiter)
    } else if seq_char_equals(&p2_chars, &seq!['S','a','t','u','r','n']) {
        Some(Planet::Saturn)
    } else if seq_char_equals(&p2_chars, &seq!['U','r','a','n','u','s']) {
        Some(Planet::Uranus)
    } else if seq_char_equals(&p2_chars, &seq!['N','e','p','t','u','n','e']) {
        Some(Planet::Neptune)
    } else {
        None
    };
    
    if p1_opt.is_none() || p2_opt.is_none() {
        return Vec::new();
    }
    
    let p1 = p1_opt.unwrap();
    let p2 = p2_opt.unwrap();
    
    let i1 = match p1 {
        Planet::Mercury => 0,
        Planet::Venus => 1,
        Planet::Earth => 2,
        Planet::Mars => 3,
        Planet::Jupiter => 4,
        Planet::Saturn => 5,
        Planet::Uranus => 6,
        Planet::Neptune => 7,
    };
    
    let i2 = match p2 {
        Planet::Mercury => 0,
        Planet::Venus => 1,
        Planet::Earth => 2,
        Planet::Mars => 3,
        Planet::Jupiter => 4,
        Planet::Saturn => 5,
        Planet::Uranus => 6,
        Planet::Neptune => 7,
    };
    
    let mut result = Vec::new();
    
    if i1 < i2 {
        let mut i = i1 + 1;
        while i <= i2 - 1
            invariant
                i1 + 1 <= i <= i2,
                result@.len() == (i - (i1 + 1)) as nat
        {
            let planet_str = if i == 0 {
                String::from("Mercury")
            } else if i == 1 {
                String::from("Venus")
            } else if i == 2 {
                String::from("Earth")
            } else if i == 3 {
                String::from("Mars")
            } else if i == 4 {
                String::from("Jupiter")
            } else if i == 5 {
                String::from("Saturn")
            } else if i == 6 {
                String::from("Uranus")
            } else {
                String::from("Neptune")
            };
            result.push(planet_str);
            i = i + 1;
        }
    } else if i1 > i2 {
        let mut i = i2 + 1;
        while i <= i1 - 1
            invariant
                i2 + 1 <= i <= i1,
                result@.len() == (i - (i2 + 1)) as nat
        {
            let planet_str = if i == 0 {
                String::from("Mercury")
            } else if i == 1 {
                String::from("Venus")
            } else if i == 2 {
                String::from("Earth")
            } else if i == 3 {
                String::from("Mars")
            } else if i == 4 {
                String::from("Jupiter")
            } else if i == 5 {
                String::from("Saturn")
            } else if i == 6 {
                String::from("Uranus")
            } else {
                String::from("Neptune")
            };
            result.push(planet_str);
            i = i + 1;
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}