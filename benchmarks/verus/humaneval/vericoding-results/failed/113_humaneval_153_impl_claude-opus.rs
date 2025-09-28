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
/* helper modified by LLM (iteration 5): Fixed integer literal syntax - removed 'int' suffix from numeric literals */
proof fn lemma_strength_computation(s: &Vec<char>, i: usize)
    requires
        0 <= i <= s@.len(),
    ensures
        strength(s@.take(i as int)) == count_upper(s@.take(i as int)) - count_lower(s@.take(i as int)),
{
    reveal(strength);
}

fn compute_strength(s: &Vec<char>) -> (result: int)
    ensures
        result == strength(s@),
{
    let mut upper_count: int = 0;
    let mut lower_count: int = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            upper_count == count_upper(s@.take(i as int)),
            lower_count == count_lower(s@.take(i as int)),
    {
        let c = s[i];
        
        proof {
            assert(s@.take((i + 1) as int) == s@.take(i as int).push(s@[i as int]));
            
            if 'A' <= c && c <= 'Z' {
                assert(count_upper(s@.take((i + 1) as int)) == count_upper(s@.take(i as int)) + 1);
                assert(count_lower(s@.take((i + 1) as int)) == count_lower(s@.take(i as int)));
            } else if 'a' <= c && c <= 'z' {
                assert(count_upper(s@.take((i + 1) as int)) == count_upper(s@.take(i as int)));
                assert(count_lower(s@.take((i + 1) as int)) == count_lower(s@.take(i as int)) + 1);
            } else {
                assert(count_upper(s@.take((i + 1) as int)) == count_upper(s@.take(i as int)));
                assert(count_lower(s@.take((i + 1) as int)) == count_lower(s@.take(i as int)));
            }
        }
        
        if 'A' <= c && c <= 'Z' {
            upper_count = upper_count + 1;
        } else if 'a' <= c && c <= 'z' {
            lower_count = lower_count + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s@.take(s@.len() as int) == s@);
    }
    
    upper_count - lower_count
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
    /* code modified by LLM (iteration 5): No changes needed in main function body */
    let mut best_idx: usize = 0;
    let mut best_strength = compute_strength(&extensions[0]);
    let mut i: usize = 1;
    
    while i < extensions.len()
        invariant
            0 <= best_idx < i <= extensions@.len(),
            best_strength == strength(extensions@[best_idx as int]@),
            forall|j: int| 0 <= j < i ==> strength(extensions@[best_idx as int]@) >= strength(extensions@[j as int]@),
            forall|j: int| 0 <= j < best_idx ==> strength(extensions@[j as int]@) < strength(extensions@[best_idx as int]@),
    {
        let curr_strength = compute_strength(&extensions[i]);
        
        if curr_strength > best_strength {
            best_strength = curr_strength;
            best_idx = i;
        }
        
        i = i + 1;
    }
    
    let mut result = Vec::new();
    let mut j: usize = 0;
    
    while j < class_name.len()
        invariant
            0 <= j <= class_name@.len(),
            result@.len() == j,
            result@ == class_name@.take(j as int),
    {
        result.push(class_name[j]);
        j = j + 1;
    }
    
    result.push('.');
    
    let mut k: usize = 0;
    while k < extensions[best_idx].len()
        invariant
            0 <= k <= extensions@[best_idx as int]@.len(),
            result@ == class_name@ + seq!['.'] + extensions@[best_idx as int]@.take(k as int),
    {
        result.push(extensions[best_idx][k]);
        k = k + 1;
    }
    
    proof {
        assert(extensions@[best_idx as int]@.take(extensions@[best_idx as int]@.len() as int) == extensions@[best_idx as int]@);
    }
    
    result
}
// </vc-code>


}

fn main() {}