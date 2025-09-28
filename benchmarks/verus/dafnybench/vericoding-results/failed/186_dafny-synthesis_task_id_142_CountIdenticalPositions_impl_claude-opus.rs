use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn count_matches_up_to(a: Seq<int>, b: Seq<int>, c: Seq<int>, n: int) -> nat
    decreases n,
{
    if n <= 0 {
        0nat
    } else {
        count_matches_up_to(a, b, c, n - 1) + 
        if a[n - 1] == b[n - 1] && b[n - 1] == c[n - 1] { 1nat } else { 0nat }
    }
}

proof fn count_matches_equiv(a: Seq<int>, b: Seq<int>, c: Seq<int>, n: int)
    requires
        a.len() == b.len(),
        b.len() == c.len(),
        0 <= n <= a.len(),
    ensures
        count_matches_up_to(a, b, c, n) == 
        Set::<int>::new(|i: int| 0 <= i < n && a[i] == b[i] && b[i] == c[i]).len(),
    decreases n,
{
    if n <= 0 {
        assert(Set::<int>::new(|i: int| 0 <= i < n && a[i] == b[i] && b[i] == c[i]) =~= Set::<int>::empty());
    } else {
        count_matches_equiv(a, b, c, n - 1);
        
        let s_prev = Set::<int>::new(|i: int| 0 <= i < n - 1 && a[i] == b[i] && b[i] == c[i]);
        let s_curr = Set::<int>::new(|i: int| 0 <= i < n && a[i] == b[i] && b[i] == c[i]);
        
        if a[n - 1] == b[n - 1] && b[n - 1] == c[n - 1] {
            assert(s_curr =~= s_prev.insert(n - 1));
            assert(!s_prev.contains(n - 1));
            assert(s_curr.len() == s_prev.len() + 1);
        } else {
            assert forall |i: int| s_curr.contains(i) <==> s_prev.contains(i) by {
                if 0 <= i < n - 1 {
                    assert(s_curr.contains(i) <==> (a[i] == b[i] && b[i] == c[i]));
                    assert(s_prev.contains(i) <==> (a[i] == b[i] && b[i] == c[i]));
                } else if i == n - 1 {
                    assert(!s_curr.contains(i));
                }
            }
            assert(s_curr =~= s_prev);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn count_identical_positions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: usize)
    requires
        a.len() == b.len() && b.len() == c.len(),
    ensures
        count >= 0,
        count == Set::<int>::new(|i: int| 0 <= i < a.len() && a[i] == b[i] && b[i] == c[i]).len(),
// </vc-spec>
// <vc-code>
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            b.len() == c.len(),
            count == count_matches_up_to(a, b, c, i as int),
    {
        if a[i] == b[i] && b[i] == c[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        count_matches_equiv(a, b, c, a.len() as int);
    }
    
    count
}
// </vc-code>

fn main() {
}

}