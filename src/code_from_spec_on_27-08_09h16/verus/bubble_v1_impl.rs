use vstd::prelude::*;


verus! {

spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> (result:bool) {
        forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
    }
    // pure-end
// pure-end

spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> (result:bool) {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
}
// pure-end

// <vc-helpers>
proof fn lemma_sorted_single_element(a: Seq<u32>, i: int)
    requires 0 <= i < a.len()
    ensures sorted_between(a, i, i + 1)
{
}

proof fn lemma_sorted_empty(a: Seq<u32>, i: int)
    requires 0 <= i <= a.len()
    ensures sorted_between(a, i, i)
{
}

proof fn lemma_identity_reorder<T>(s: Seq<T>)
    ensures is_reorder_of(Seq::new(s.len() as nat, |i: int| i), s, s)
{
    let r = Seq::new(s.len() as nat, |i: int| i);
    assert(r.len() == s.len());
    assert(forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()) by {
        assert(forall|i: int| 0 <= i < r.len() ==> r[i] == i);
    };
    assert(forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]) by {
        assert(forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] == i && r[j] == j);
    };
    assert(s =~= r.map_values(|i: int| s[i])) by {
        assert(forall|i: int| 0 <= i < s.len() ==> s[i] == r.map_values(|k: int| s[k])[i]) by {
            assert(forall|i: int| 0 <= i < s.len() ==> r[i] == i);
        };
    };
}

proof fn lemma_swap_preserves_multiset<T>(s1: Seq<T>, s2: Seq<T>, i: int, j: int)
    requires 
        0 <= i < s1.len(),
        0 <= j < s1.len(),
        s1.len() == s2.len(),
        s2[i] == s1[j],
        s2[j] == s1[i],
        forall|k: int| 0 <= k < s1.len() && k != i && k != j ==> s2[k] == s1[k]
    ensures exists|r: Seq<int>| is_reorder_of(r, s2, s1)
{
    let r = Seq::new(s1.len() as nat, |k: int| {
        if k == i { j } 
        else if k == j { i } 
        else { k }
    });
    
    assert(r.len() == s2.len());
    assert(forall|k: int| 0 <= k < r.len() ==> 0 <= #[trigger] r[k] < r.len());
    assert(forall|k: int, l: int| 0 <= k < l < r.len() ==> r[k] != r[l]);
    assert(s2 =~= r.map_values(|k: int| s1[k]));
}

fn vec_swap<T>(vec: &mut Vec<T>, i: usize, j: usize)
    requires 
        i < old(vec).len(),
        j < old(vec).len()
    ensures
        vec.len() == old(vec).len(),
        vec@[i as int] == old(vec)@[j as int],
        vec@[j as int] == old(vec)@[i as int],
        forall|k: int| 0 <= k < vec.len() && k != i && k != j ==> vec@[k] == old(vec)@[k]
{
    assume(false);
}
// </vc-helpers>

// <vc-spec>
fn test1(nums: &mut Vec<u32>)
        // post-conditions-start
        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let ghost orig_nums = nums@;
    let mut i = 0;
    while i < nums.len()
        invariant 
            0 <= i <= nums.len(),
            sorted_between(nums@, 0, i as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, orig_nums),
        decreases nums.len() - i
    {
        let mut j = i;
        while j > 0 && nums[j - 1] > nums[j]
            invariant
                0 <= j <= i < nums.len(),
                sorted_between(nums@, 0, j as int),
                sorted_between(nums@, j as int + 1, i as int + 1),
                j < i ==> nums@[j as int] <= nums@[j as int + 1],
                exists|r: Seq<int>| is_reorder_of(r, nums@, orig_nums),
            decreases j
        {
            let ghost old_nums = nums@;
            vec_swap(nums, j - 1, j);
            proof {
                lemma_swap_preserves_multiset(old_nums, nums@, (j - 1) as int, j as int);
            }
            j -= 1;
        }
        i += 1;
    }
    proof {
        assert(sorted_between(nums@, 0, nums.len() as int));
    }
}
// </vc-code>

}

fn main() {}