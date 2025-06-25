// ATOM 
pub open spec fn sorted(a: &[int]) -> bool {
    sortedA(a, a.len())
}

// ATOM 
pub open spec fn sortedA(a: &[int], i: int) -> bool
    requires 0 <= i <= a.len()
{
    forall|k: int| 0 < k < i ==> a[k-1] <= a[k]
}

// SPEC 
pub fn lookForMin(a: &[int], i: int) -> (m: int)
    requires 0 <= i < a.len()
    ensures i <= m < a.len()
    ensures forall|k: int| i <= k < a.len() ==> a[k] >= a[m]
{
}

// SPEC 
pub fn insertionSort(a: &mut [int])
    ensures sorted(a)
{
}