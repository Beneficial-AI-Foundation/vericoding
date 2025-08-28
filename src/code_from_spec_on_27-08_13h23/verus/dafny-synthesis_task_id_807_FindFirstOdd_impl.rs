use vstd::prelude::*;

verus! {

spec fn is_odd(x: int) -> bool {
    x % 2 != 0
}

// <vc-helpers>
proof fn lemma_seq_index<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s[i as usize] == s@[i],
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_first_odd(a: &[i32]) -> (result: (bool, usize))
    ensures 
        (!result.0 ==> (forall|i: int| 0 <= i < a.len() ==> !is_odd(a[i] as int))) &&
        (result.0 ==> (0 <= result.1 < a.len() && 
                      is_odd(a[result.1 as int] as int) && 
                      (forall|i: int| 0 <= i < result.1 ==> !is_odd(a[i] as int))))
// </vc-spec>
// </vc-spec>

// <vc-code>
fn find_first_odd(a: &[i32]) -> (result: (bool, usize))
    ensures 
        (!result.0 ==> (forall|i: int| 0 <= i < a.len() ==> !is_odd(a[i] as int))) &&
        (result.0 ==> (0 <= result.1 < a.len() && 
                      is_odd(a[result.1] as int) && 
                      (forall|i: int| 0 <= i < result.1 ==> !is_odd(a[i] as int)))),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> !is_odd(a[k as usize] as int),
    {
        if is_odd(a[i] as int) {
            return (true, i);
        }
        i = i + 1;
    }
    (false, 0)
}
// </vc-code>

fn main() {}

}