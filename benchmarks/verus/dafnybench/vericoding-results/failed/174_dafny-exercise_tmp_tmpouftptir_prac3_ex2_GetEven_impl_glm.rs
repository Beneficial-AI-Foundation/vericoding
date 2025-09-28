use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_odd(n: nat) -> bool {
    n % 2 == 1
}

spec fn even(n: nat) -> nat {
    if is_odd(n) { n + 1 } else { n }
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
    let n = s.len();
    let ghost old_s = s@;
    for i in 0..n
        invariant
            forall|j: int| 0 <= j < i ==> s@[j] == even(old_s[j]),
            forall|j: int| i <= j < n ==> s@[j] == old_s[j],
            s.len() == n,
    {
        if old_s[i] % 2 == 1 {
            proof {
                assert(is_odd(old_s[i]));
            }
            s[i] = old_s[i] + 1;
        } else {
            proof {
                assert(!is_odd(old_s[i]));
            }
        }
    }
}
// </vc-code>

fn main() {
}

}