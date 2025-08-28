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
proof fn lemma_all_equal_empty()
    ensures all_equal(Seq::<i32>::empty())
{
}

proof fn lemma_all_equal_single(x: i32)
    ensures all_equal(seq![x])
{
}

proof fn lemma_all_equal_extend(s: Seq<i32>, x: i32)
    requires all_equal(s)
    ensures all_equal(s.push(x)) <==> (s.len() == 0 || s[0] == x)
{
}

proof fn lemma_all_equal_first(s: Seq<i32>)
    requires s.len() > 0
    ensures all_equal(s) <==> (forall|i: int| #[trigger] s[i] == s[0] => 0 <= i < s.len() ==> s[i] == s[0])
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn mall_equal1(v: &[i32]) -> (b: bool)
    ensures b == all_equal(v@)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if v.len() == 0 {
        proof {
            lemma_all_equal_empty();
        }
        return true;
    }
    
    if v.len() == 1 {
        proof {
            lemma_all_equal_single(v[0]);
        }
        return true;
    }
    
    let first = v[0];
    let mut i = 1;
    
    while i < v.len()
        invariant 
            0 <= i <= v.len(),
            forall|j: int| #[trigger] v@[j] => 0 <= j < i ==> v@[j] == first
        ensures
            i == v.len(),
            forall|j: int| #[trigger] v@[j] => 0 <= j < i ==> v@[j] == first
        decreases v.len() - i
    {
        if v[i] != first {
            proof {
                lemma_all_equal_first(v@);
                assert(!all_equal(v@));
            }
            return false;
        }
        i += 1;
    }
    
    proof {
        lemma_all_equal_first(v@);
        assert(forall|j: int| #[trigger] v@[j] => 0 <= j < v@.len() ==> v@[j] == first);
        assert(all_equal(v@));
    }
    true
}
// </vc-code>

fn main() {
}

}