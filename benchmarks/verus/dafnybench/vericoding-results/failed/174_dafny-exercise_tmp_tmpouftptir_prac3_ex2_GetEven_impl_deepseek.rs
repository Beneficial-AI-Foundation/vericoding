use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn update_preserves_len(s: Seq<nat>, s_prime: Seq<nat>)
    ensures
        s_prime.len() == s.len(),
{
}

proof fn update_even_condition(s: Seq<nat>, s_prime: Seq<nat>)
    ensures
        forall|i: int| 0 <= i < s.len() ==> {
            if s[i] % 2 == 1 {
                s_prime[i] == s[i] + 1
            } else {
                s_prime[i] == s[i]
            }
        },
{
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
    let old_s = s@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() == old_s.len(),
            forall|j: int| 0 <= j < i ==> {
                if old_s[j] % 2 == 1 {
                    s@[j] == old_s[j] + 1
                } else {
                    s@[j] == old_s[j]
                }
            },
            forall|j: int| i <= j < s.len() ==> s@[j] == old_s[j],
    {
        let idx = i;
        proof {
            assert(0 <= idx < s.len());
        }
        if old_s[idx] % 2 == 1 {
            let val = s[idx];
            s.set(idx, val + 1);
        }
        i = i + 1;
    }
    proof {
        update_preserves_len(old_s, s@);
        update_even_condition(old_s, s@);
    }
}
// </vc-code>

fn main() {
}

}