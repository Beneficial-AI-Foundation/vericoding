// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_sub_list(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)

    requires
        sub.len() <= main.len(),

    ensures
        result == (exists|k: int, l: int|
            0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && (#[trigger] (main@.subrange(
                k,
                l,
            ))) =~= sub@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop syntax error - removed invariant_except_break */
    if sub.len() == 0 {
        assert(main@.subrange(0, 0) =~= sub@);
        return true;
    }
    
    if main.len() < sub.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i <= main.len() - sub.len()
        invariant
            i <= main.len() - sub.len() + 1,
            sub.len() <= main.len(),
            sub.len() > 0,
            forall|k: int| 0 <= k < i as int ==> main@.subrange(k, k + sub.len() as int) != sub@,
        decreases (main.len() - sub.len() + 1) - i
    {
        let mut j: usize = 0;
        let mut matches = true;
        
        while j < sub.len()
            invariant
                j <= sub.len(),
                i <= main.len() - sub.len(),
                i + j <= main.len(),
                matches == (forall|m: int| 0 <= m < j as int ==> main@[i as int + m] == sub@[m]),
            ensures
                j <= sub.len(),
                matches ==> j == sub.len(),
                matches == (forall|m: int| 0 <= m < j as int ==> main@[i as int + m] == sub@[m]),
            decreases sub.len() - j
        {
            if main[i + j] != sub[j] {
                matches = false;
                break;
            }
            j = j + 1;
        }
        
        if matches {
            assert(j == sub.len());
            assert(forall|m: int| 0 <= m < sub.len() as int ==> main@[i as int + m] == sub@[m]);
            assert(main@.subrange(i as int, i as int + sub.len() as int) =~= sub@);
            return true;
        }
        
        i = i + 1;
    }
    
    false
}
// </vc-code>

}
fn main() {}