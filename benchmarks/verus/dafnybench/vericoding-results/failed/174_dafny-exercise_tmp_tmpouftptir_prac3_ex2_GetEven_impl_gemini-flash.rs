use vstd::prelude::*;

verus! {

// <vc-helpers>
fn get_even_helper(val: &mut nat)
    ensures
        if *old(val) % 2 == 1 {
            *val == *old(val) + 1
        } else {
            *val == *old(val)
        }
{
    if (*val % 2) as int == 1 {
        *val = *val + 1;
    }
}
// </vc-helpers>

// <vc-spec>
fn get_even(s: &mut Vec<nat>)
    ensures 
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < s.len() ==> {
            if old(s)[i] % 2 == 1 {
                s[i] == old(s)[i] + 1
            } else {
                s[i] == old(s)[i]
            }
        }
// </vc-spec>
// <vc-code>
{
    let old_s_len = s.len();
    let old_s_contents = s.clone();

    let mut i: usize = 0;
    while i < s.len()
        invariant
            s.len() == old_s_len,
            0 <= i && i <= s.len(),
            forall|j: int| 0 <= j < i ==> {
                if old_s_contents@[j] % 2 == 1 {
                    s@[j] == old_s_contents@[j] + 1
                } else {
                    s@[j] == old_s_contents@[j]
                }
            }
    {
        proof {
            assert(i < old_s_len); // For s.get_by_index
            assert(i < s.len()); // For s[i]
        }
        let old_val = s[i];
        get_even_helper(&mut s[i]);
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}