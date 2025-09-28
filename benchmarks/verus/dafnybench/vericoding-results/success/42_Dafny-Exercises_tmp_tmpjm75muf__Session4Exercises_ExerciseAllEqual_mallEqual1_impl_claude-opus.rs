use vstd::prelude::*;

verus! {

spec fn all_equal(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}
//forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] == s[j]
//forall|i: int| 0 < i < s.len() ==> s[i-1] == s[i]
//forall|i: int| 0 <= i < s.len() - 1 ==> s[i] == s[i+1]


//Ordered indexes

//All equal to first

// <vc-helpers>
proof fn all_equal_means_equal_to_first(s: Seq<i32>)
    requires
        s.len() > 0,
        all_equal(s),
    ensures
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == s[0],
{
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] == s[0] by {
        assert(all_equal(s));
        assert(0 <= 0 < s.len() && 0 <= i < s.len() ==> s[0] == s[i]);
    }
}

proof fn equal_to_first_means_all_equal(s: Seq<i32>)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == s[0],
    ensures
        all_equal(s),
{
    assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() implies #[trigger] s[i] == #[trigger] s[j] by {
        assert(s[i] == s[0]);
        assert(s[j] == s[0]);
    }
}
// </vc-helpers>

// <vc-spec>
fn mall_equal1(v: &[i32]) -> (b: bool)
    ensures b == all_equal(v@)
// </vc-spec>
// <vc-code>
{
    if v.len() == 0 {
        return true;
    }
    
    let first = v[0];
    let mut i: usize = 1;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] v@[j] == first,
            first == v@[0],
        decreases v.len() - i,
    {
        if v[i] != first {
            // Found an element different from the first
            assert(v@[i as int] != v@[0]);
            assert(!(all_equal(v@)));
            return false;
        }
        i = i + 1;
    }
    
    // All elements equal to first, so all are equal
    assert(forall|j: int| 0 <= j < v@.len() ==> #[trigger] v@[j] == first);
    proof {
        equal_to_first_means_all_equal(v@);
    }
    true
}
// </vc-code>

fn main() {
}

}