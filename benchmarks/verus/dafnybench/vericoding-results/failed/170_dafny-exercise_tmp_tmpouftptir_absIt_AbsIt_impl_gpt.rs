use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let ghost old_s: Seq<i32> = s@;
    let n: usize = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            s.len() == n,
            0 <= i as int <= n as int,
            forall|j: int| 0 <= j < i as int ==>
                if old_s[j] < 0 { s@[j] == -old_s[j] } else { s@[j] == old_s[j] },
            forall|j: int| i as int <= j < n as int ==>
                s@[j] == old_s[j]
        decreases (n as int - i as int)
    {
        let x: i32 = s[i];
        if x < 0 {
            s.set(i, -x);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}