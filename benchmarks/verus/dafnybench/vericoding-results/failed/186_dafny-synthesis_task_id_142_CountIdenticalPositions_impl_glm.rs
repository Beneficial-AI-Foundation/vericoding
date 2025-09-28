use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_count_identical_positions(a: Seq<int>, b: Seq<int>, c: Seq<int>, i: int, count: int)
    requires
        0 <= i <= a.len(),
        a.len() == b.len() && b.len() == c.len(),
        count == Set::<int>::new(|k: int| 0 <= k < i && a[k] == b[k] && b[k] == c[k]).len(),
    ensures
        count >= 0,
        count == Set::<int>::new(|k: int| 0 <= k < i && a[k] == b[k] && b[k] == c[k]).len(),
    decreases i,
{
    if i == 0 {
        assert(Set::<int>::new(|k: int| false).len() == 0);
    } else {
        let cond = a[i-1] == b[i-1] && b[i-1] == c[i-1];
        let s_i = Set::<int>::new(|k: int| 0 <= k < i && a[k] == b[k] && b[k] == c[k]);
        let s_i_minus_1 = Set::<int>::new(|k: int| 0 <= k < i-1 && a[k] == b[k] && b[k] == c[k]);
        let s_singleton = if cond { Set::singleton(i-1) } else { Set::empty() };
        
        assert forall |k: int| #[trigger] s_i.contains(k) == (s_i_minus_1.contains(k) || s_singleton.contains(k)) by {
            if s_i.contains(k) {
                if k == i-1 {
                    assert(s_singleton.contains(k));
                } else {
                    assert(s_i_minus_1.contains(k));
                }
            } else {
                if s_i_minus_1.contains(k) || s_singleton.contains(k) {
                    if k == i-1 {
                        assert(cond);
                        assert(s_i.contains(k));
                    } else {
                        assert(s_i.contains(k));
                    }
                }
            }
        }
        
        assert forall |k: int| #[trigger] s_i_minus_1.contains(k) && s_singleton.contains(k) ==> false by {
            if s_i_minus_1.contains(k) && s_singleton.contains(k) {
                assert(k == i-1);
                assert(0 <= k < i-1);
                assert(false);
            }
        }
        
        assert(s_i.len() == s_i_minus_1.len() + s_singleton.len());
        
        lemma_count_identical_positions(a, b, c, i-1, count - (if cond { 1 } else { 0 }));
        
        assert(s_singleton.len() == (if cond { 1 } else { 0 }));
        assert(s_i.len() == (count - (if cond { 1 } else { 0 })) + (if cond { 1 } else { 0 }));
        assert(s_i.len() == count);
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
    let n = a.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= (i as int) <= (n as int),
            count == Set::<int>::new(|k: int| 0 <= k < (i as int) && a[k] == b[k] && b[k] == c[k]).len(),
            count >= 0,
    {
        if a@[i as int] == b@[i as int] && b@[i as int] == c@[i as int] {
            count = count + 1;
        }
        i = i + 1;
        proof {
            lemma_count_identical_positions(a, b, c, i as int, count as int);
        }
    }
    count
}
// </vc-code>

fn main() {
}

}