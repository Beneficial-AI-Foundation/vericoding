// ATOM 
spec fn sorted(a: &[i32], l: int, u: int) -> bool
{
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i] <= a[j]
}

// ATOM 
spec fn partitioned(a: &[i32], i: int) -> bool
{
    forall|k: int, k_prime: int| 0 <= k <= i < k_prime < a.len() ==> a[k] <= a[k_prime]
}

// SPEC 
pub fn BubbleSort(a: &mut [i32])
{
}

// SPEC 
pub fn Main()
{
}