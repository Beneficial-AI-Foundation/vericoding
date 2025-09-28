// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_vowel(c: char) -> bool {
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>
fn is_upper_vowel_exec(c: char) -> bool
{
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}

/* helper modified by LLM (iteration 4): Added lemma to prove empty set has length 0 */
proof fn lemma_empty_set_len()
    ensures Set::<int>::new(|j: int| 0 <= j < 0 && j % 2 == 0 && is_upper_vowel('A')).len() == 0
{
    let s = Set::<int>::new(|j: int| 0 <= j < 0 && j % 2 == 0 && is_upper_vowel('A'));
    assert(forall|j: int| !s.contains(j));
    assert(s =~= Set::<int>::empty());
}
// </vc-helpers>

// <vc-spec>
fn count_upper(s: Vec<char>) -> (cnt: usize)
    ensures cnt == Set::<int>::new(|i: int| 0 <= i < s@.len() && i % 2 == 0 && is_upper_vowel(s@[i])).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed invariant initialization and overflow handling */
    let mut cnt: usize = 0;
    let mut i: usize = 0;
    
    proof {
        let init_set = Set::<int>::new(|j: int| 0 <= j < 0 && j % 2 == 0 && is_upper_vowel(s@[j]));
        assert(forall|j: int| !init_set.contains(j));
        assert(init_set =~= Set::<int>::empty());
        assert(init_set.len() == 0);
    }
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            cnt == Set::<int>::new(|j: int| 0 <= j < i && j % 2 == 0 && is_upper_vowel(s@[j])).len(),
            cnt <= s.len(),
        decreases s.len() - i
    {
        if i % 2 == 0 && is_upper_vowel_exec(s[i]) {
            cnt = cnt + 1;
            
            proof {
                let old_set = Set::<int>::new(|j: int| 0 <= j < i && j % 2 == 0 && is_upper_vowel(s@[j]));
                let new_set = Set::<int>::new(|j: int| 0 <= j < i + 1 && j % 2 == 0 && is_upper_vowel(s@[j]));
                
                assert(is_upper_vowel(s@[i as int]));
                assert(new_set.contains(i as int));
                assert(forall|j: int| old_set.contains(j) ==> new_set.contains(j));
                assert(forall|j: int| new_set.contains(j) && j != i ==> old_set.contains(j));
                assert(new_set =~= old_set.insert(i as int));
                assert(!old_set.contains(i as int));
                assert(new_set.len() == old_set.len() + 1);
                assert(new_set.len() <= s.len());
            }
        } else {
            proof {
                let old_set = Set::<int>::new(|j: int| 0 <= j < i && j % 2 == 0 && is_upper_vowel(s@[j]));
                let new_set = Set::<int>::new(|j: int| 0 <= j < i + 1 && j % 2 == 0 && is_upper_vowel(s@[j]));
                
                assert(forall|j: int| old_set.contains(j) ==> new_set.contains(j));
                assert(forall|j: int| new_set.contains(j) ==> old_set.contains(j));
                assert(old_set =~= new_set);
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == s.len());
    }
    
    cnt
}
// </vc-code>


}

fn main() {}