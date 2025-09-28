// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max_value(s: Seq<char>) -> int {
    max_value_up_to_index(s, s.len() as int)
}

spec fn max_value_up_to_index(s: Seq<char>, up_to: int) -> int
    decreases up_to when 0 <= up_to <= s.len()
{
    if up_to == 0 { 0 }
    else {
        let current_value = current_value_at_index(s, up_to);
        let max_before = max_value_up_to_index(s, up_to - 1);
        if current_value > max_before { current_value } else { max_before }
    }
}

spec fn current_value_at_index(s: Seq<char>, index: int) -> int
    decreases index when 0 <= index <= s.len()
{
    if index == 0 { 0 }
    else { 
        current_value_at_index(s, index - 1) + (if s[index - 1 as nat] == 'I' { 1 } else { -1 })
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemmas to prove bounds on current_value and max_value */

proof fn lemma_current_value_bounded(s: Seq<char>, index: int)
    requires
        0 <= index <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == 'I' || s[i] == 'D',
    ensures
        -index <= current_value_at_index(s, index) <= index,
    decreases index
{
    if index == 0 {
        // Base case: current_value_at_index(s, 0) == 0
    } else {
        lemma_current_value_bounded(s, index - 1);
        // current_value_at_index(s, index) = current_value_at_index(s, index - 1) + (if s[index - 1] == 'I' { 1 } else { -1 })
        // By IH: -(index - 1) <= current_value_at_index(s, index - 1) <= index - 1
        // If s[index - 1] == 'I': -index + 1 + 1 <= result <= index - 1 + 1, so -index + 2 <= result <= index
        // If s[index - 1] == 'D': -index + 1 - 1 <= result <= index - 1 - 1, so -index <= result <= index - 2
        // In both cases: -index <= result <= index
    }
}

proof fn lemma_max_value_bounded(s: Seq<char>, up_to: int)
    requires
        0 <= up_to <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == 'I' || s[i] == 'D',
    ensures
        0 <= max_value_up_to_index(s, up_to) <= up_to,
    decreases up_to
{
    if up_to == 0 {
        // Base case: max_value_up_to_index(s, 0) == 0
    } else {
        lemma_current_value_bounded(s, up_to);
        lemma_max_value_bounded(s, up_to - 1);
        // max_value_up_to_index(s, up_to) = max(current_value_at_index(s, up_to), max_value_up_to_index(s, up_to - 1))
        // By lemmas: -up_to <= current_value_at_index(s, up_to) <= up_to
        //           0 <= max_value_up_to_index(s, up_to - 1) <= up_to - 1
        // Therefore: 0 <= max_value_up_to_index(s, up_to) <= up_to
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: Vec<char>) -> (result: i8)
    requires 
        1 <= n <= 100,
        n as int == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> s@[i] == 'I' || s@[i] == 'D',
    ensures 
        result >= 0,
        result as int == max_value(s@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added proof blocks with lemma calls to maintain invariants */
    let mut current_value: i8 = 0;
    let mut max_value: i8 = 0;
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            i <= n as usize,
            n as int == s@.len(),
            forall|j: int| 0 <= j < s@.len() ==> s@[j] == 'I' || s@[j] == 'D',
            current_value as int == current_value_at_index(s@, i as int),
            max_value as int == max_value_up_to_index(s@, i as int),
            max_value >= 0,
            current_value >= -(i as int),
            current_value <= i as int,
            max_value <= i as int,
        decreases n as usize - i
    {
        if s[i] == 'I' {
            current_value = current_value + 1;
        } else {
            current_value = current_value - 1;
        }
        
        if current_value > max_value {
            max_value = current_value;
        }
        
        i = i + 1;
        
        proof {
            lemma_current_value_bounded(s@, i as int);
            lemma_max_value_bounded(s@, i as int);
        }
    }
    
    proof {
        lemma_max_value_bounded(s@, n as int);
    }
    
    max_value
}
// </vc-code>


}

fn main() {}