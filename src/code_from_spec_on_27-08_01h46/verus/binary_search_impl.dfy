use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn lemma_sorted_property(v: &Vec<u64>, i: int, j: int, k: int)
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        0 <= i <= k <= j < v.len(),
    ensures
        v[i] <= v[k] <= v[j],
{
}

proof fn lemma_element_exists(v: &Vec<u64>, k: u64, low: int, high: int) -> (result: int)
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i:int| 0 <= i < v.len() && k == v[i],
        0 <= low <= high < v.len(),
        v[low] <= k <= v[high],
    ensures
        low <= result <= high,
        k == v[result],
{
    let witness_i = choose|i:int| 0 <= i < v.len() && k == v[i];
    
    if witness_i < low {
        lemma_sorted_property(v, witness_i, low, low);
        assert(v[witness_i] <= v[low]);
        assert(k == v[witness_i]);
        assert(k <= v[low]);
        assert(v[low] <= k);
        assert(false);
        low
    } else if witness_i > high {
        lemma_sorted_property(v, high, witness_i, witness_i);
        assert(v[high] <= v[witness_i]);
        assert(k == v[witness_i]);
        assert(v[high] <= k);
        assert(k <= v[high]);
        assert(false);
        high
    } else {
        witness_i
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search(v: &Vec<u64>, k: u64) -> (result:usize)
    // pre-conditions-start
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i:int| 0 <= i < v.len() && k == v[i],
    // pre-conditions-end
    // post-conditions-start
    ensures
        result < v.len(),
        k == v[result as int],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut low: usize = 0;
    let mut high: usize = v.len() - 1;
    
    while low < high
        invariant
            low <= high,
            high < v.len(),
            forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
            exists|i:int| (low as int) <= i <= (high as int) && k == v[i],
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if v[mid] == k {
            return mid;
        } else if v[mid] < k {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    assert(low == high);
    assert(exists|i:int| (low as int) <= i <= (high as int) && k == v[i]);
    
    proof {
        let witness = choose|i:int| (low as int) <= i <= (high as int) && k == v[i];
        assert((low as int) <= witness <= (high as int));
        assert(low as int == high as int);
        assert(witness == low as int);
        assert(k == v[witness]);
        assert(k == v[low as int]);
    }
    
    low
}
// </vc-code>

}

fn main() {}