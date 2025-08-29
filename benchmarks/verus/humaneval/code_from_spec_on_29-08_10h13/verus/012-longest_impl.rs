use vstd::prelude::*;

verus! {

spec fn expr_inner_longest(strings: &Vec<Vec<u8>>, result: Option<&Vec<u8>>) -> (result: bool) {
    match result {
        None => strings.len() == 0,
        Some(s) => {
            (forall|i: int| #![auto] 0 <= i < strings.len() ==> s.len() >= strings[i].len())
                && (exists|i: int|
                #![auto]
                (0 <= i < strings.len() && s == strings[i] && (forall|j: int|
                    #![auto]
                    0 <= j < i ==> strings[j].len() < s.len())))
        },
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_longest_correct(strings: &Vec<Vec<u8>>, max_idx: usize)
    requires
        strings.len() > 0,
        max_idx < strings.len(),
        forall|i: int| #![auto] 0 <= i < strings.len() ==> strings[max_idx as int].len() >= strings[i].len(),
        forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() < strings[max_idx as int].len(),
    ensures
        expr_inner_longest(strings, Some(&strings[max_idx as int])),
{
    let result = Some(&strings[max_idx as int]);
    match result {
        Some(s) => {
            assert(forall|i: int| #![auto] 0 <= i < strings.len() ==> s.len() >= strings[i].len());
            /* code modified by LLM (iteration 3): fixed syntax error by removing 'by' block from assert exists */
            assert(exists|i: int| #![auto] 
                (0 <= i < strings.len() && s == strings[i] && 
                 (forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() < s.len())));
        }
        None => {}
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def longest(strings: List[str]) -> Optional[str]"
docstring: |
Out of list of strings, return the longest one. Return the first one in case of multiple
strings of the same length. Return None in case the input list is empty.
test_cases:
- input: []
expected_output: None
- input: ["a", "b", "c"]
expected_output: "a"
- input: ["a", "bb", "ccc"]
expected_output: "ccc"
*/
// </vc-description>

// <vc-spec>
fn longest(strings: &Vec<Vec<u8>>) -> (result: Option<&Vec<u8>>)
    // post-conditions-start
    ensures
        expr_inner_longest(strings, result),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    if strings.len() == 0 {
        return None;
    }
    
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    /* code modified by LLM (iteration 3): added decreases clause to satisfy Verus verification requirements */
    while i < strings.len()
        invariant
            strings.len() > 0,
            max_idx < strings.len(),
            i <= strings.len(),
            forall|k: int| #![auto] 0 <= k < i ==> strings[max_idx as int].len() >= strings[k].len(),
            forall|j: int| #![auto] 0 <= j < max_idx ==> strings[j].len() < strings[max_idx as int].len(),
        decreases strings.len() - i
    {
        if strings[i].len() > strings[max_idx].len() {
            max_idx = i;
        }
        i += 1;
    }
    
    proof {
        lemma_longest_correct(strings, max_idx);
    }
    
    Some(&strings[max_idx])
}
// </vc-code>

}
fn main() {}