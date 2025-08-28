use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn is_sorted(v: &Vec<u64>) -> bool {
    forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j]
}

spec fn contains_key(v: &Vec<u64>, k: u64) -> bool {
    exists|i:int| 0 <= i < v.len() && k == v[i]
}

proof fn sorted_implies_range_property(v: &Vec<u64>, k: u64, mid: int)
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        0 <= mid < v.len(),
    ensures
        v[mid] < k ==> forall|i:int| 0 <= i <= mid ==> v[i] <= k,
        v[mid] > k ==> forall|i:int| mid <= i < v.len() ==> v[i] >= k,
{
}

proof fn sorted_property_helper(v: &Vec<u64>, i: int, j: int, k: u64)
    requires
        forall|x:int, y:int| 0 <= x <= y < v.len() ==> v[x] <= v[y],
        0 <= i <= j < v.len(),
        v[j] < k,
    ensures
        v[i] <= v[j],
        v[i] < k,
{
}

proof fn sorted_property_helper2(v: &Vec<u64>, i: int, j: int, k: u64)
    requires
        forall|x:int, y:int| 0 <= x <= y < v.len() ==> v[x] <= v[y],
        0 <= i <= j < v.len(),
        v[i] > k,
    ensures
        v[i] <= v[j],
        v[j] > k,
{
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
    let mut high: usize = v.len();
    
    while low < high
        invariant
            0 <= low <= high <= v.len(),
            forall|i:int| 0 <= i < low ==> v[i] < k,
            forall|i:int| high <= i < v.len() ==> v[i] > k,
            exists|i:int| low <= i < high && k == v[i],
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        
        if v[mid] == k {
            return mid;
        } else if v[mid] < k {
            proof {
                assert(forall|i:int| 0 <= i < low ==> v[i] < k);
                assert(v[mid as int] < k);
                assert(low <= mid < high);
                assert(forall|i:int| low <= i <= mid ==> {
                    sorted_property_helper(v, i, mid as int, k);
                    v[i] < k
                });
            }
            low = mid + 1;
        } else {
            proof {
                assert(forall|i:int| high <= i < v.len() ==> v[i] > k);
                assert(v[mid as int] > k);
                assert(low <= mid < high);
                assert(forall|i:int| mid <= i < high ==> {
                    sorted_property_helper2(v, mid as int, i, k);
                    v[i] > k
                });
            }
            high = mid;
        }
    }
    
    low
}
// </vc-code>

}

fn main() {}