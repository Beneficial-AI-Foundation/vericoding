use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn firstE(a: &[char]) -> (x: i32)
    ensures
        if a@.contains('e') {
            0 <= x < a@.len() && a@[x as int] == 'e' && 
            forall|i: int| 0 <= i < x ==> a@[i] != 'e'
        } else {
            x == -1
        }
// </vc-spec>
// <vc-code>
{
    let n_usize: usize = a.len();
    let n: int = n_usize as int;
    let mut i: int = 0;
    let mut iu: usize = 0;
    while iu < n_usize
        invariant 0 <= i && i <= n;
        invariant iu <= n_usize;
        invariant iu == (i as usize);
        invariant forall |j: int| 0 <= j && j < i ==> a@[j] != 'e';
        decreases n - i;
    {
        if a[iu] == 'e' {
            return i as i32;
        } else {
            i = i + 1;
            iu = iu + 1;
        }
    }
    return -1;
}
// </vc-code>

fn main() {
}

}