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
proof fn count_upper_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires s1.len() <= s2.len(),
             s2.take(s1.len() as int) == s1
    ensures count_upper(s1) <= count_upper(s2)
    decreases s2.len()
{
    if s1.len() == 0 {
    } else if s1.len() == s2.len() {
    } else {
        count_upper_monotonic(s1, s2.drop_last());
    }
}

proof fn count_lower_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires s1.len() <= s2.len(),
             s2.take(s1.len() as int) == s1
    ensures count_lower(s1) <= count_lower(s2)
    decreases s2.len()
{
    if s1.len() == 0 {
    } else if s1.len() == s2.len() {
    } else {
        count_lower_monotonic(s1, s2.drop_last());
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
{
    /* code modified by LLM (iteration 5): fixed type conversion in sequence access */
    let mut best_idx: usize = 0;
    let ghost mut best_strength = strength(extensions@[0]@);
    
    let mut i = 1;
    while i < extensions.len()
        invariant
            0 <= i <= extensions.len(),
            0 <= best_idx < i,
            best_strength == strength(extensions@[best_idx as int]@),
            forall|j: int| 0 <= j < i ==> strength(extensions@[j]@) <= best_strength,
            forall|j: int| 0 <= j < best_idx ==> strength(extensions@[j]@) < best_strength
    {
        let ghost current_strength = strength(extensions@[i]@);
        if current_strength > best_strength {
            best_idx = i;
            best_strength = current_strength;
        }
        i += 1;
    }
    
    let mut result = class_name;
    result.push('.');
    result.extend_from_slice(&extensions[best_idx]);
    
    result
}
// </vc-code>


}

fn main() {}