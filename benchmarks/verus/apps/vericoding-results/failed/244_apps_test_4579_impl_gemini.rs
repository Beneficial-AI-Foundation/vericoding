// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn distinct_strings(strings: Seq<String>) -> Set<String> {
    Set::new(|s: String| exists|i: int| 0 <= i < strings.len() && strings[i] == s)
}

spec fn valid_input(strings: Seq<String>) -> bool {
    strings.len() >= 1
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_distinct_strings_is_to_set(strings: Seq<String>)
    ensures
        distinct_strings(strings) == strings.to_set(),
{
    assert_sets_equal!(distinct_strings(strings), strings.to_set());
}

fn vec_contains(haystack: &Vec<String>, needle: &String) -> (found: bool)
    ensures
        found == haystack@.contains(*needle),
{
    let mut i = 0;
    while i < haystack.len()
        invariant
            0 <= i <= haystack.len(),
            !haystack@.subrange(0, i as int).contains(*needle),
        decreases haystack.len() - i
    {
        if haystack[i] == *needle {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-helpers>

// <vc-spec>
fn solve(strings: Vec<String>) -> (count: i8)
    requires 
        valid_input(strings@)
    ensures 
        count as int >= 1,
        count as int <= strings@.len(),
        count as int == distinct_strings(strings@).len()
// </vc-spec>
// <vc-code>
{
    let mut unique_strings: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            forall|j: int, k: int| 0 <= j < k < unique_strings@.len() ==> unique_strings@[j] != unique_strings@[k],
            unique_strings@.to_set() == strings@.subrange(0, i as int).to_set(),
        decreases strings.len() - i
    {
        let current_string = &strings[i];
        let found = vec_contains(&unique_strings, current_string);
        
        let s_prefix = strings@.subrange(0, i as int);
        if !found {
            proof {
                assert(!unique_strings@.contains(*current_string));
                assert(!s_prefix.contains(*current_string));
                vstd::seq_lib::lemma_to_set_push_not_contains(s_prefix, *current_string);
            }
            unique_strings.push(current_string.clone());
        } else {
            proof {
                assert(unique_strings@.contains(*current_string));
                assert(s_prefix.contains(*current_string));
                vstd::seq_lib::lemma_to_set_push_contains(s_prefix, *current_string);
            }
        }
        i = i + 1;
    }

    proof {
        vstd::seq_lib::lemma_len_to_set_distinct(unique_strings@);
        lemma_distinct_strings_is_to_set(strings@);
        assert(unique_strings@.to_set() == strings@.to_set());
        assert(unique_strings@.len() as int == distinct_strings(strings@).len());
    }

    let count = unique_strings.len();
    return count as i8;
}
// </vc-code>


}

fn main() {}