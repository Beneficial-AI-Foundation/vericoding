use vstd::prelude::*;

verus! {
    spec fn strict_negative(v: &Vec<i32>, i: int, j: int) -> bool
        recommends 0 <= i <= j <= v.len()
    {
        forall|u: int| i <= u < j ==> v[u] < 0
    }

    spec fn positive(s: Seq<i32>) -> bool {
        forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
    }

    spec fn is_permutation(s: Seq<i32>, t: Seq<i32>) -> bool {
        s.to_multiset() == t.to_multiset()
    }

    // Basic working version that demonstrates the translation structure
    fn separate(v: &mut Vec<i32>) -> (result: usize)
        requires old(v).len() > 0
        ensures result <= v.len()
        ensures strict_negative(v, 0, result as int)
        ensures positive(v@.subrange(result as int, v.len() as int))
        ensures is_permutation(old(v)@, v@)
    {
        let mut left = 0;
        let mut right = v.len();
        
        while left < right
            invariant 0 <= left <= right <= v.len()
            invariant strict_negative(v, 0, left as int)
            invariant positive(v@.subrange(right as int, v.len() as int))
            invariant is_permutation(old(v)@, v@)
        {
            if v[left] < 0 {
                left += 1;
            } else {
                right -= 1;
                v.swap(left, right);
            }
        }
        
        left
    }

    fn main() {}
}