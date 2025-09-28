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
    let old_s = s.clone();
    let n: usize = s.len();
    let mut i: usize = 0;
    while i < n
        invariant { i <= n }
        invariant { s.len() == old_s.len() }
        invariant { forall|j: int| 0 <= j && j < (i as int) ==>
            (if old_s@[j] % 2 == 1 {
                s@[j] == old_s@[j] + 1
            } else {
                s@[j] == old_s@[j]
            })
        }
        decreases { n - i }
    {
        let v = s[i];
        if v % 2 == 1 {
            s[i] = v + 1;
        }
        i += 1;
    }

    // final assertions to help verifier (these follow from the loop invariant at i == n)
    assert(s.len() == old_s.len());
    assert(forall|j: int| 0 <= j && j < (n as int) ==>
        (if old_s@[j] % 2 == 1 {
            s@[j] == old_s@[j] + 1
        } else {
            s@[j] == old_s@[j]
        })
    );
}
// </vc-code>

fn main() {
}

}