use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn monotonic_lemma(l: Vec<i32>, i: int, j: int, b: bool)
    requires
        0 <= i < j < l@.len(),
        b <==> (forall|k: int, m: int| 0 <= k < m < l@.len() ==> l@.index(k) <= l@.index(m)),
    ensures
        b ==> l@.index(i) <= l@.index(j)
{
    if b {
        forall|k: int, m: int| 0 <= k < m < l@.len() ==> l@.index(k) <= l@.index(m);
        assert(l@.index(i) <= l@.index(j));
    }
}

proof fn antimonotonic_lemma(l: Vec<i32>, i: int, j: int, b: bool)
    requires
        0 <= i < j < l@.len(),
        b <==> (forall|k: int, m: int| 0 <= k < m < l@.len() ==> l@.index(k) >= l@.index(m)),
    ensures
        b ==> l@.index(i) >= l@.index(j)
{
    if b {
        forall|k: int, m: int| 0 <= k < m < l@.len() ==> l@.index(k) >= l@.index(m);
        assert(l@.index(i) >= l@.index(j));
    }
}
// </vc-helpers>

// <vc-spec>
fn monotonic(l: Vec<i32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = l.len();
    if n <= 1 {
        true
    } else {
        let mut increasing = true;
        let mut decreasing = true;
        let mut i = 0;
        
        while i < n - 1
            invariant
                0 <= i < n,
                increasing <==> (forall|k: int, m: int| 0 <= k < m <= i ==> l@.index(k) <= l@.index(m)),
                decreasing <==> (forall|k: int, m: int| 0 <= k < m <= i ==> l@.index(k) >= l@.index(m)),
            decreases n - 1 - i,
        {
            if l[i] > l[i + 1] {
                increasing = false;
            }
            if l[i] < l[i + 1] {
                decreasing = false;
            }
            i = i + 1;
        }
        
        increasing || decreasing
    }
}
// </vc-code>

fn main() {}
}