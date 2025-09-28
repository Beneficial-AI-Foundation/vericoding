use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let one: nat = 1;
    let two: nat = 2;

    let mut i: usize = 0;
    while i < s.len()
        invariant
            s.len() == old(s).len(),
            0 <= i as int <= s.len() as int,
            forall|j: int| 0 <= j < i as int ==> {
                if old(s)[j] % two == one {
                    #[trigger] s[j] == old(s)[j] + one
                } else {
                    #[trigger] s[j] == old(s)[j]
                }
            },
            forall|j: int| i as int <= j < s.len() as int ==> #[trigger] s[j] == old(s)[j]
    {
        let cur = s[i];
        assert(i < s.len());
        assert(s[i] == old(s)[i]);

        let parity_is_odd = cur % two == one;
        let newv = if parity_is_odd { cur + one } else { cur };

        if parity_is_odd {
            assert(old(s)[i] % two == one);
            assert(newv == old(s)[i] + one);
        } else {
            assert(!(old(s)[i] % two == one));
            assert(newv == old(s)[i]);
        }

        s.set(i, newv);
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}