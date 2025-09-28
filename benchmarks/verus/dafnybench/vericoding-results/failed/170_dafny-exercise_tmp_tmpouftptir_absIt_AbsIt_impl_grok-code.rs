use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
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
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len() as int,
            forall|k: int| 0 <= k < i ==> #[trigger] s@[k] == (if old(s)@[k] < 0 { -old(s)@[k] } else { old(s)@[k] })
        decreases s.len() as int - i
    {
        s[i] = if s[i] < 0 { -s[i] } else { s[i] };
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}