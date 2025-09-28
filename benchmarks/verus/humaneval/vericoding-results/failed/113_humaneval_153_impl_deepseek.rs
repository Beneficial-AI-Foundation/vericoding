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

proof fn lemma_strength_ge(s: Seq<char>, t: Seq<char>)
    requires strength(s) >= strength(t)
    ensures forall|u: Seq<char>| strength(s + u) >= strength(t + u)
{
    assert forall|u: Seq<char>| strength(s + u) == strength(s) + strength(u) by {
        assert(count_upper(s + u) == count_upper(s) + count_upper(u));
        assert(count_lower(s + u) == count_lower(s) + count_lower(u));
    };
    assert forall|u: Seq<char>| strength(t + u) == strength(t) + strength(u) by {
        assert(count_upper(t + u) == count_upper(t) + count_upper(u));
        assert(count_lower(t + u) == count_lower(t) + count_lower(u));
    };
}

proof fn lemma_strength_extension_ordering(i: int, j: int, extensions: Seq<Seq<char>>, class_name: Seq<char>)
    requires 0 <= i < extensions.len(), 0 <= j < extensions.len()
    ensures strength(extensions[i]) >= strength(extensions[j]) ==>
            strength(class_name + seq!['.'] + extensions[i]) >= strength(class_name + seq!['.'] + extensions[j])
{
    lemma_strength_ge(extensions[i], extensions[j]);
    assert(strength(class_name + seq!['.']) == strength(class_name) + strength(seq!['.']));
}

proof fn find_max_ensures_property(extensions: Seq<Seq<char>>, best_index: int)
    requires 0 <= best_index < extensions.len()
    ensures forall|j: int| 0 <= j < best_index ==> strength(extensions[j]) < strength(extensions[best_index])
    decreases extensions.len() - best_index
{
    if best_index > 0 {
        find_max_ensures_property(extensions, best_index - 1);
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
    /* code modified by LLM (iteration 5): Fixed integer literal syntax and added proof support */
    let mut max_strength: int = -1000000;
    let mut best_index: usize = 0;
    let mut i: usize = 0;
    
    while i < extensions.len()
        invariant
            0 <= i <= extensions@.len(),
            best_index < extensions@.len(),
            forall|j: int| 0 <= j < i as int ==> strength(extensions@[best_index as int]@) >= strength(extensions@[j]@),
            forall|j: int| 0 <= j < best_index as int ==> strength(extensions@[j]@) < strength(extensions@[best_index as int]@)
        decreases extensions@.len() - i as int
    {
        let current_strength = strength(extensions[i]@);
        if current_strength > max_strength {
            max_strength = current_strength;
            best_index = i;
            proof { find_max_ensures_property(extensions@.take(i as int), best_index as int); }
        } else if current_strength == max_strength {
            if i < best_index {
                best_index = i;
            }
        }
        i = i + 1;
    }
    
    let mut result = class_name.clone();
    result.push('.');
    result.extend(extensions[best_index].iter().copied());
    result
}
// </vc-code>


}

fn main() {}