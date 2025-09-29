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
proof fn all_equal_empty()
    ensures all_equal(Seq::<i32>::empty())
{
}

proof fn all_equal_single(x: i32)
    ensures all_equal(seq![x])
{
}

proof fn all_equal_extend(s: Seq<i32>, x: i32)
    requires all_equal(s), s.len() > 0, s[0] == x
    ensures all_equal(s.push(x))
{
}

proof fn all_equal_first_element(s: Seq<i32>)
    requires all_equal(s), s.len() > 0
    ensures forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == s[0]
{
}

proof fn first_element_all_equal(s: Seq<i32>)
    requires forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == s[0]
    ensures all_equal(s)
{
}
// </vc-helpers>

// <vc-spec>
fn mall_equal1(v: &[i32]) -> (b: bool)
    ensures b == all_equal(v@)
// </vc-spec>
// <vc-code>
{
    if v.len() == 0 {
        proof { all_equal_empty(); }
        return true;
    }
    
    if v.len() == 1 {
        proof { all_equal_single(v[0]); }
        return true;
    }
    
    let first = v[0];
    let mut i = 1;
    
    while i < v.len()
        invariant 
            0 < i <= v.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] v@[k] == first
        decreases v.len() - i
    {
        if v[i] != first {
            assert(v@[0] == first);
            assert(v@[i as int] != first);
            assert(exists|j: int, k: int| 0 <= j < v@.len() && 0 <= k < v@.len() && v@[j] != v@[k]);
            proof {
                assert(!all_equal(v@)) by {
                    assert(v@[0] != v@[i as int]);
                }
            }
            return false;
        }
        i += 1;
    }
    
    proof { 
        assert(forall|k: int| 0 <= k < v@.len() ==> #[trigger] v@[k] == first);
        first_element_all_equal(v@);
    }
    true
}
// </vc-code>

fn main() {
}

}