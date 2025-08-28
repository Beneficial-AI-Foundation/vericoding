use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn lemma_midpoint(low: int, high: int)
    requires
        low <= high,
    ensures
        low <= (low + high) / 2 <= high,
{
    // Proof by simple arithmetic
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
fn binary_search(v: &Vec<u64>, k: u64) -> (result: usize)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i: int| 0 <= i < v.len() && k == v[i],
    ensures
        result < v.len(),
        k == v[result as int],
{
    let mut low: usize = 0;
    let mut high: usize = v.len() - 1;
    
    while low <= high
        invariant
            0 <= low as int <= v.len() as int,
            0 <= high as int < v.len() as int,
            low <= high ==> (forall|i: int, j: int| low as int <= i <= j <= high as int ==> v[i] <= v[j]),
            exists|i: int| low as int <= i <= high as int && k == v[i],
        decreases
            high - low,
    {
        let mid = (low + high) / 2;
        proof {
            lemma_midpoint(low as int, high as int);
        }
        if v[mid] == k {
            return mid;
        } else if v[mid] < k {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    // This line should not be reached due to the precondition ensuring k exists
    unreachable!();
}
// </vc-code>

}

fn main() {}