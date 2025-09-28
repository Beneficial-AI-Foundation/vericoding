// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_vowel(c: char) -> bool {
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no changes required for this helper function */
fn is_upper_vowel_exec(c: char) -> (res: bool)
    ensures
        res == is_upper_vowel(c),
{
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-helpers>

// <vc-spec>
fn count_upper(s: Vec<char>) -> (cnt: usize)
    ensures cnt == Set::<int>::new(|i: int| 0 <= i < s@.len() && i % 2 == 0 && is_upper_vowel(s@[i])).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed compilation error by using `==` for set equality instead of `.ext_equal()` */
    let mut i: usize = 0;
    let mut cnt: usize = 0;

    proof {
        let s_spec = s@;
        let set_at_0 = Set::<int>::new(|k: int| 0 <= k < 0 && k % 2 == 0 && is_upper_vowel(s_spec[k]));
        assert(set_at_0 == Set::empty());
        assert(set_at_0.len() == 0);
    }

    while i < s.len()
        invariant
            i <= s.len(),
            cnt <= i,
            cnt == Set::<int>::new(|k: int| 0 <= k < (i as int) && k % 2 == 0 && is_upper_vowel(s@[k])).len(),
        decreases s.len() - i
    {
        if i % 2 == 0 {
            if is_upper_vowel_exec(s[i]) {
                cnt = cnt + 1;
            }
        }
        
        proof {
            let i_old = i as int;
            
            let set_old = Set::<int>::new(|k: int| 0 <= k < i_old && k % 2 == 0 && is_upper_vowel(s@[k]));
            let set_new = Set::<int>::new(|k: int| 0 <= k < i_old + 1 && k % 2 == 0 && is_upper_vowel(s@[k]));
            
            let char_at_i_spec = s@[i_old];
            let is_match = i % 2 == 0 && is_upper_vowel(char_at_i_spec);

            vstd::set_lib::lemma_set_properties::<int>();

            if is_match {
                assert(set_new == set_old.insert(i_old));
            } else {
                assert(set_new == set_old);
            }
        }

        i = i + 1;
    }
    cnt
}
// </vc-code>


}

fn main() {}