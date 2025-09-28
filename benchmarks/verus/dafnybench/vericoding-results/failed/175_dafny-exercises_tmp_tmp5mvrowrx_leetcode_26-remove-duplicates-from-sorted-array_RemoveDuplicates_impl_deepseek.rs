use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn sorted_contains_subrange(seq: Seq<i32>, subrange: Seq<i32>, len: nat) -> bool {
    &&& len <= seq.len()
    &&& forall|i: int| 0 <= i < len as int ==> #[trigger] subrange.index(i) == seq.index(i)
    &&& forall|i: int| 0 <= i < len as int ==> #[trigger] seq.contains(subrange.index(i))
}

proof fn lemma_unique_subrange_preserves_contains(seq: Seq<i32>, subrange: Seq<i32>, len: nat, x: i32)
    requires
        sorted_contains_subrange(seq, subrange, len),
        seq.contains(x),
    ensures
        len > 0 ==> subrange.subrange(0, len as int).contains(x)
{
    if len > 0 {
        assert(0 <= len as int && len as int <= subrange.len());
        assert(subrange.subrange(0, len as int).len() == len as int);
        assert(forall|i: int| 0 <= i < len as int ==> subrange.subrange(0, len as int)[i] == subrange[i]);
        assert(seq.contains(x));
        
        let mut k: int = 0;
        while k < seq.len()
            invariant
                0 <= k <= seq.len(),
                forall|m: int| 0 <= m < k ==> seq[m] != x,
            decreases seq.len() - k,
        {
            if seq[k] == x {
                assert(k < len as int ==> subrange[k] == x);
                assert(k >= len as int ==> {
                    let found_index = find_index_in_subrange(subrange, len, x);
                    found_index < len as int && subrange[found_index] == x
                });
                break;
            }
            k = k + 1;
        }
    }
}

spec fn find_index_in_subrange(subrange: Seq<i32>, len: nat, x: i32) -> int
    recommends len > 0
{
    choose|i: int| 0 <= i < len as int && subrange[i] == x
}

spec fn is_sorted(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] <= seq[j]
}

spec fn is_unique(seq: Seq<i32>, len: nat) -> bool {
    forall|i: int, j: int| 0 <= i < j < len as int ==> seq[i] != seq[j]
}

proof fn lemma_sorted_unique_contains(seq: Seq<i32>, subrange: Seq<i32>, len: nat)
    requires
        is_sorted(seq),
        sorted_contains_subrange(seq, subrange, len),
        is_unique(subrange, len),
    ensures
        forall|i: int| 0 <= i < seq.len() ==> (len > 0 ==> subrange.subrange(0, len as int).contains(seq[i]))
{
    if len > 0 {
        assert(0 <= len as int && len as int <= subrange.len());
        assert(subrange.subrange(0, len as int).len() == len as int);
        assert(forall|k: int| 0 <= k < len as int ==> subrange.subrange(0, len as int)[k] == subrange[k]);
        
        let mut i: int = 0;
        while i < seq.len()
            invariant
                0 <= i <= seq.len(),
                forall|j: int| 0 <= j < i ==> (len > 0 ==> subrange.subrange(0, len as int).contains(seq[j])),
            decreases seq.len() - i,
        {
            if len > 0 {
                assert(seq.contains(seq[i]));
                lemma_unique_subrange_preserves_contains(seq, subrange, len, seq[i]);
            }
            i = i + 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(nums: &mut Vec<i32>) -> (num_length: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < old(nums).len() ==> old(nums)[i] <= old(nums)[j],
    ensures
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums[i] != nums[j],
        forall|i: int| 0 <= i < num_length ==> old(nums)@.contains(nums[i]),
        forall|i: int| 0 <= i < old(nums).len() ==> nums@.subrange(0, num_length as int).contains(old(nums)[i]),
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    if n == 0 {
        proof {
            assert(nums@.subrange(0, 0).len() == 0) by (compute);
            assert(forall|i: int, j: int| 0 <= i < j < 0 ==> nums[i] != nums[j]) by (compute);
            assert(forall|i: int| 0 <= i < 0 ==> old(nums)@.contains(nums[i])) by (compute);
            assert(forall|i: int| 0 <= i < old(nums)@.len() ==> nums@.subrange(0, 0 as int).contains(old(nums)[i])) by {
                assert forall|i: int| 0 <= i < old(nums)@.len() implies nums@.subrange(0, 0 as int).contains(old(nums)[i]) by {
                    assert(false); // Empty subrange cannot contain anything
                };
            };
        }
        return 0;
    }
    
    let mut i: usize = 0;
    let mut j: usize = 1;
    
    while j < n
        invariant
            i < n,
            j <= n,
            i < j,
            sorted_contains_subrange(old(nums)@, nums@, (i + 1) as nat),
            is_unique(nums@, (i + 1) as nat),
        decreases n - j,
    {
        if nums[j] != nums[i] {
            i = i + 1;
            nums[i] = nums[j];
            proof {
                assert(nums@[i as int] == old(nums)@[j as int]);
                assert(forall|k: int| 0 <= k < i + 1 ==> old(nums)@.contains(nums@[k]));
                assert(forall|k: int, l: int| 0 <= k < l < i + 1 ==> nums@[k] != nums@[l]);
            }
        }
        j = j + 1;
    }
    
    proof {
        lemma_sorted_unique_contains(old(nums)@, nums@, (i + 1) as nat);
    }
    
    i + 1
}
// </vc-code>

fn main() {
}

}