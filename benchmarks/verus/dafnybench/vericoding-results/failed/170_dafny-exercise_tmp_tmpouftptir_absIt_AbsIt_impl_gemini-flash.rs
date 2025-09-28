use vstd::prelude::*;

verus! {

// <vc-helpers>
fn abs(x: int) -> (y: int)
    ensures
        y == if x < 0 { -x } else { x }
{
    if x < 0 {
        -x
    } else {
        x
    }
}
// </vc-helpers>

// <vc-spec>
fn abs_it(s: &mut Vec<i32>)
    ensures
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if old(s)[i] < 0 { s[i] == -old(s)[i] } else { s[i] == old(s)[i] }
// </vc-spec>
// <vc-code>
{
    let old_s_len = s.len();
    let old_s = s.clone();
    let mut i = 0;
    while i < s.len()
        invariant
            s.len() == old_s_len,
            0 <= i as int <= s.len() as int,
            forall|j: int| 0 <= j < i ==>
                if old_s@[j] < 0 { s@[j] == -old_s@[j] } else { s@[j] == old_s@[j] }
    {
        proof {
            assert(s@[i] is int); // Prove that s@[i] can be safely converted to int
        }
        s.set(i, abs(s@[i] as int) as i32);
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}