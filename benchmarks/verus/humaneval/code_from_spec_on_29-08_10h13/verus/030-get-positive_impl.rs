use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn all_positive(s: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] > 0
}

/* code modified by LLM (iteration 5): fixed lemma with proper sequence filter reasoning */
proof fn filter_subrange_lemma(s: Seq<i32>, i: int)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i + 1).filter(|y: i32| y > 0) == 
            if s[i] > 0 { s.subrange(0, i).filter(|y: i32| y > 0).push(s[i]) }
            else { s.subrange(0, i).filter(|y: i32| y > 0) }
{
    let prefix = s.subrange(0, i);
    let element = s[i];
    let extended = s.subrange(0, i + 1);
    
    assert(extended == prefix.push(element));
    
    if element > 0 {
        assert forall |x: i32| extended.contains(x) && x > 0 <==> 
            (prefix.contains(x) && x > 0) || x == element;
        assert(extended.filter(|y: i32| y > 0).len() == prefix.filter(|y: i32| y > 0).len() + 1);
        
        let filtered_prefix = prefix.filter(|y: i32| y > 0);
        let filtered_extended = extended.filter(|y: i32| y > 0);
        
        assert forall |j: int| 0 <= j < filtered_prefix.len() ==> 
            filtered_extended[j] == filtered_prefix[j];
        assert(filtered_extended[filtered_prefix.len()] == element);
        assert(filtered_extended == filtered_prefix.push(element));
    } else {
        assert forall |x: i32| extended.contains(x) && x > 0 <==> 
            prefix.contains(x) && x > 0;
        assert(extended.filter(|y: i32| y > 0) == prefix.filter(|y: i32| y > 0));
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def get_positive(l: list)"
docstring: |
Return only positive numbers in the list.
test_cases:
- input: [-1, 2, -4, 5, 6]
expected_output: [2, 5, 6]
- input: [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
expected_output: [5, 3, 2, 3, 9, 123, 1]
*/
// </vc-description>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    /* code modified by LLM (iteration 5): added proof block inside loop to apply lemma correctly */
    while i < input.len()
        invariant
            i <= input.len(),
            result@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
        decreases input.len() - i,
    {
        proof {
            filter_subrange_lemma(input@, i as int);
        }
        
        if input[i] > 0 {
            result.push(input[i]);
        }
        i += 1;
    }
    
    proof {
        assert(i == input.len());
        assert(input@.subrange(0, i as int) == input@);
    }
    
    result
}
// </vc-code>

}
fn main() {}