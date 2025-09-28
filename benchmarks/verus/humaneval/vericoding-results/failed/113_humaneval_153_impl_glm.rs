// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_upper(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if 'A' <= s[0] && s[0] <= 'Z' { 1int } else { 0int }) + count_upper(s.skip(1))
    }
}

spec fn count_lower(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if 'a' <= s[0] && s[0] <= 'z' { 1int } else { 0int }) + count_lower(s.skip(1))
    }
}

spec fn strength(s: Seq<char>) -> int {
    count_upper(s) - count_lower(s)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed integer type suffixes */
fn exec_strength(s: &[char]) -> (result: int)
    ensures
        result == strength(s@),
    decreases
        s.len()
{
    if s.len() == 0 {
        0int
    } else {
        let first = s[0];
        let rest_strength = exec_strength(&s[1..]);
        let mut add = 0int;
        if 'A' <= first && first <= 'Z' {
            add = 1int;
        } else if 'a' <= first && first <= 'z' {
            add = -1int;
        }
        add + rest_strength
    }
}
// </vc-helpers>

// <vc-spec>
fn strongest_extension(class_name: Vec<char>, extensions: Vec<Vec<char>>) -> (result: Vec<char>)
    requires extensions@.len() > 0
    ensures exists|i: int| 0 <= i < extensions@.len() && 
            result@ == class_name@ + seq!['.'] + extensions@[i]@ &&
            (forall|j: int| 0 <= j < extensions@.len() ==> 
                strength(extensions@[i]@) >= strength(extensions@[j]@)) &&
            (forall|j: int| 0 <= j < i ==> 
                strength(extensions@[j]@) < strength(extensions@[i]@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed sequence access for strength function */
{
    let mut best_index = 0;
    let mut best_strength = exec_strength(&extensions[0]);
    let mut i = 1;
    while i < extensions.len()
        invariant
            0 <= i <= extensions.len(),
            best_index < i,
            best_strength == strength(extensions@[best_index]@),
            (forall|j: int| 0 <= j < i ==> 
                strength(extensions@[j]@) <= best_strength),
            (forall|j: int| 0 <= j < best_index ==> 
                strength(extensions@[j]@) < best_strength),
        decreases extensions.len() - i
    {
        let current_strength = exec_strength(&extensions[i]);
        if current_strength > best_strength {
            best_strength = current_strength;
            best_index = i;
        }
        i += 1;
    }
    let mut result = class_name;
    result.push('.');
    result.extend(extensions[best_index].clone());
    result
}
// </vc-code>


}

fn main() {}