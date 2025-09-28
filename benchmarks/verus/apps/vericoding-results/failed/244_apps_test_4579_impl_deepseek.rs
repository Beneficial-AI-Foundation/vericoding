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

/* helper modified by LLM (iteration 5): Fix clone usage in proof context */
proof fn distinct_strings_len_lemma(strings: Seq<String>, i: int, j: int) 
    ensures 
        0 <= i <= j <= strings.len() ==> distinct_strings(strings.subrange(i, j)).len() <= distinct_strings(strings.subrange(i, j + 1)).len(),
        0 <= i <= j <= strings.len() ==> distinct_strings(strings.subrange(i, j)).len() <= distinct_strings(strings).len()
{
}

proof fn distinct_strings_single_lemma(s: String) 
    ensures 
        distinct_strings(Seq::new(1, |k: int| s)).len() == 1
{
}

proof fn distinct_strings_empty_lemma() 
    ensures 
        distinct_strings(Seq::empty()).len() == 0
{
}

fn count_distinct_helper(strings: &Vec<String>, start: usize, end: usize) -> (count: i8)
    requires 
        start <= end <= strings@.len(),
        valid_input(strings@)
    ensures 
        count as int >= 0,
        count as int <= distinct_strings(strings@).len(),
        count as int == distinct_strings(strings@.subrange(start as int, end as int)).len()
    decreases end - start
{
    if start == end {
        proof { distinct_strings_empty_lemma(); }
        0
    } else {
        let current_str = strings[start].clone();
        let mut seen = false;
        let mut i = start + 1;
        
        while i < end
            invariant 
                i >= start + 1,
                i <= end,
                seen == exists|j: int| start + 1 <= j < i && strings@[j] == current_str
        {
            if strings[i] == current_str {
                seen = true;
                break;
            }
            i += 1;
        }
        
        let rest_count = count_distinct_helper(strings, start + 1, end);
        
        if seen {
            rest_count
        } else {
            proof { distinct_strings_single_lemma(current_str); }
            (rest_count + 1) as i8
        }
    }
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
    /* code modified by LLM (iteration 5): Remove unnecessary proof calls and fix lemma parameters */
    let count = count_distinct_helper(&strings, 0, strings.len());
    count
}
// </vc-code>


}

fn main() {}