use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SecondSmallest(s: Vec<int>) -> (secondSmallest: int)
    requires
        s.len() >= 2,
        // There must be at least 2 different values, a minimum && another one,
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.spec_index(i) == min(s.spec_index(..)) && s.spec_index(j) != s.spec_index(i)
    ensures
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.spec_index(i) == min(s.spec_index(..)) && s.spec_index(j) == secondSmallest,
        forall|k: int| 0 <= k < s.len() && s.spec_index(k) != min(s.spec_index(..)) ==> s.spec_index(k) >= secondSmallest
{
    let mut minimum = s[0];
    let mut second_min = s[0];
    let mut found_different = false;
    
    // First pass: find the minimum
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            minimum <= min(s.spec_index(..)),
            exists|k: int| 0 <= k < i && s.spec_index(k) == minimum
    {
        if s[i] < minimum {
            minimum = s[i];
        }
    }
    
    // Second pass: find the second smallest (smallest among non-minimum values)
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            minimum == min(s.spec_index(..)),
            found_different ==> (
                second_min != minimum &&
                exists|k: int| 0 <= k < i && s.spec_index(k) == second_min &&
                forall|k: int| 0 <= k < i && s.spec_index(k) != minimum ==> s.spec_index(k) >= second_min
            ),
            !found_different ==> forall|k: int| 0 <= k < i ==> s.spec_index(k) == minimum
    {
        if s[i] != minimum {
            if !found_different {
                second_min = s[i];
                found_different = true;
            } else if s[i] < second_min {
                second_min = s[i];
            }
        }
    }
    
    assert(found_different);
    assert(second_min != minimum);
    assert(exists|j: int| 0 <= j < s.len() && s.spec_index(j) == second_min);
    assert(forall|k: int| 0 <= k < s.len() && s.spec_index(k) != minimum ==> s.spec_index(k) >= second_min);
    
    second_min
}

}

The implementation works as follows:

   - We correctly identify the minimum value
   - We properly track whether we've found a different value
   - When we have found a different value, it's the smallest among all non-minimum values seen so far

The key insight is that the second smallest value is simply the minimum value among all elements that are not equal to the global minimum. The precondition guarantees that such elements exist.