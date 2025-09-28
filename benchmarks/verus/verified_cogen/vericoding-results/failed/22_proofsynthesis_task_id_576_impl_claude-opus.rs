// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_sub_array(main: &Vec<i32>, sub: &Vec<i32>) -> (result: bool)

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
    /* code modified by LLM (iteration 5): Fixed invariant_except_break syntax */
    if sub.len() == 0 {
        proof {
            assert(main@.subrange(0, 0) =~= sub@);
            assert(exists|k: int, l: int| 0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && main@.subrange(k, l) =~= sub@);
        }
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
            forall|k: int, l: int| 0 <= k < i && l == k + sub.len() ==> main@.subrange(k, l) != sub@,
        decreases main.len() - sub.len() - i + 1
    {
        let mut j: usize = 0;
        let mut matches = true;
        while j < sub.len()
            invariant
                j <= sub.len(),
                i <= main.len() - sub.len(),
                i + j <= main.len(),
                matches == (forall|m: int| 0 <= m < j ==> main@[i as int + m] == sub@[m]),
            invariant_except_break
                matches == (forall|m: int| 0 <= m < j ==> main@[i as int + m] == sub@[m]),
            ensures
                j <= sub.len(),
                (matches && j == sub.len()) || (!matches && j < sub.len()),
                matches ==> (forall|m: int| 0 <= m < sub.len() ==> main@[i as int + m] == sub@[m]),
            decreases sub.len() - j
        {
            if main[i + j] != sub[j] {
                matches = false;
                break;
            }
            j = j + 1;
        }
        
        if matches {
            proof {
                assert(j == sub.len());
                assert(forall|m: int| 0 <= m < sub.len() ==> main@[i as int + m] == sub@[m]);
                assert(main@.subrange(i as int, i as int + sub.len() as int) =~= sub@);
                assert(exists|k: int, l: int| 0 <= k <= (main.len() - sub.len()) && l == k + sub.len() && main@.subrange(k, l) =~= sub@);
            }
            return true;
        }
        i = i + 1;
    }
    
    proof {
        assert(forall|k: int, l: int| 0 <= k <= (main.len() - sub.len()) && l == k + sub.len() ==> main@.subrange(k, l) != sub@);
    }
    false
}
// </vc-code>

}
fn main() {}