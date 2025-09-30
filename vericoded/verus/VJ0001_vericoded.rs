// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
spec fn binary_search_index(v: Seq<u64>, k: u64, low: int, high: int) -> int
    decreases high - low
{
    if low >= high {
        low
    } else {
        let mid = low + (high - low) / 2;
        if v[mid] < k {
            binary_search_index(v, k, mid + 1, high)
        } else if v[mid] > k {
            binary_search_index(v, k, low, mid)
        } else {
            mid
        }
    }
}

proof fn binary_search_index_correct(v: Seq<u64>, k: u64, low: int, high: int)
    requires
        0 <= low <= high <= v.len(),
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i: int| low <= i < high && k == v[i],
    ensures
        low <= binary_search_index(v, k, low, high) < high,
        v[binary_search_index(v, k, low, high)] == k,
    decreases high - low
{
    if low >= high {
    } else {
        let mid = low + (high - low) / 2;
        if v[mid] < k {
            binary_search_index_correct(v, k, mid + 1, high);
        } else if v[mid] > k {
            binary_search_index_correct(v, k, low, mid);
        } else {
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search(v: &Vec<u64>, k: u64) -> (result:usize)

    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i:int| 0 <= i < v.len() && k == v[i],

    ensures
        result < v.len(),
        k == v[result as int],
// </vc-spec>
// <vc-code>
{
    let mut low: usize = 0;
    let mut high: usize = v.len();
    
    while low < high
        invariant
            0 <= low <= high <= v.len(),
            forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
            exists|i: int| low <= i < high && k == v[i as int],
            binary_search_index(v@, k, low as int, high as int) == binary_search_index(v@, k, 0, v.len() as int),
        decreases high - low
    {
        let mid: usize = low + (high - low) / 2;
        
        if v[mid] < k {
            low = mid + 1;
        } else if v[mid] > k {
            high = mid;
        } else {
            proof {
                binary_search_index_correct(v@, k, 0, v.len() as int);
            }
            return mid;
        }
    }
    
    proof {
        binary_search_index_correct(v@, k, 0, v.len() as int);
    }
    low
}
// </vc-code>

}
fn main() {}