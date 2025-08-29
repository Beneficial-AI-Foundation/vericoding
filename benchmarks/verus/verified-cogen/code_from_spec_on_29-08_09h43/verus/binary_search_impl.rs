use vstd::prelude::*;

verus!{

// <vc-helpers>
fn forall_less_than_preserved(v: &Vec<u64>, k: u64, low: usize, mid: usize)
    requires
        forall|i:int| 0 <= i < low ==> v[i] < k,
        v[mid as int] < k,
        mid as int >= low,
    ensures
        forall|i:int| 0 <= i < (mid + 1) as int ==> v[i] < k,
{
    assert forall|i:int| 0 <= i < (mid + 1) as int implies v[i] < k by {
        if i < low {
            assert(v[i] < k);
        } else if i == mid as int {
            assert(v[i] < k);
        } else {
            assert(0 <= i < low || i == mid as int);
            assert(v[i] < k);
        }
    }
}

fn forall_greater_than_preserved(v: &Vec<u64>, k: u64, mid: usize, high: usize)
    requires
        forall|i:int| high <= i < v.len() ==> v[i] > k,
        v[mid as int] > k,
        mid as int < high,
    ensures
        forall|i:int| mid <= i < v.len() ==> v[i] > k,
{
    assert forall|i:int| mid <= i < v.len() implies v[i] > k by {
        if i >= high {
            assert(v[i] > k);
        } else if i == mid as int {
            assert(v[i] > k);
        } else {
            assert(i >= high || i == mid as int);
            assert(v[i] > k);
        }
    }
}

fn exists_in_range_after_low_update(v: &Vec<u64>, k: u64, low: usize, mid: usize, high: usize)
    requires
        exists|i:int| low <= i < high && k == v[i],
        v[mid as int] < k,
        mid as int >= low && mid as int < high,
    ensures
        exists|i:int| (mid + 1) as int <= i < high && k == v[i],
{
    let witness = choose|i:int| low <= i < high && k == v[i];
    if witness <= mid as int {
        assert(k == v[witness] && v[witness] < k);
        assert(false);
    } else {
        assert((mid + 1) as int <= witness < high && k == v[witness]);
    }
}

fn exists_in_range_after_high_update(v: &Vec<u64>, k: u64, low: usize, mid: usize, high: usize)
    requires
        exists|i:int| low <= i < high && k == v[i],
        v[mid as int] > k,
        mid as int >= low && mid as int < high,
    ensures
        exists|i:int| low <= i < mid && k == v[i],
{
    let witness = choose|i:int| low <= i < high && k == v[i];
    if witness >= mid as int {
        assert(k == v[witness] && v[witness] > k);
        assert(false);
    } else {
        assert(low <= witness < mid && k == v[witness]);
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    let mut high: usize = v.len();
    
    /* code modified by LLM (iteration 5): fixed invariant syntax by removing invalid forall statement */
    while low < high
        invariant
            low <= high <= v.len(),
            forall|i:int| 0 <= i < low ==> v[i] < k,
            forall|i:int| high <= i < v.len() ==> v[i] > k,
            exists|i:int| low <= i < high && k == v[i],
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if v[mid] < k {
            proof {
                forall_less_than_preserved(v, k, low, mid);
                exists_in_range_after_low_update(v, k, low, mid, high);
            }
            low = mid + 1;
        } else if v[mid] > k {
            proof {
                forall_greater_than_preserved(v, k, mid, high);
                exists_in_range_after_high_update(v, k, low, mid, high);
            }
            high = mid;
        } else {
            return mid;
        }
    }
    
    unreached()
}
// </vc-code>

}

fn main() {}