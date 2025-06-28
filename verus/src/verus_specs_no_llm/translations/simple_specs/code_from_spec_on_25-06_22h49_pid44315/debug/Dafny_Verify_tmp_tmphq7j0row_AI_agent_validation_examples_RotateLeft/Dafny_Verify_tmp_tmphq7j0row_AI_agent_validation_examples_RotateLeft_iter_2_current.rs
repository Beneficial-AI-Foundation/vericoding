use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Find maximum value in a non-empty vector
fn max_vec(a: Vec<nat>) -> (m: nat)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> a[i] <= m
    ensures exists|i: int| 0 <= i < a.len() && m == a[i]
{
    let mut m = a[0];
    let mut idx = 1;
    
    while idx < a.len()
        invariant 
            1 <= idx <= a.len(),
            forall|i: int| 0 <= i < idx ==> a[i] <= m,
            exists|i: int| 0 <= i < idx && m == a[i]
    {
        if a[idx] > m {
            m = a[idx];
        }
        idx = idx + 1;
    }
    
    m
}

// Compute cube of a natural number
fn cube(n: nat) -> (c: nat) 
    ensures c == n * n * n
{
    n * n * n
}

// Recursive power function (2^n)
spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power(n - 1) }
}

// Compute 2^n iteratively
fn compute_power(n: nat) -> (y: nat)
    ensures y == power(n)
{
    let mut result = 1;
    let mut i = 0;
    
    while i < n
        invariant 
            0 <= i <= n,
            result == power(i)
    {
        result = result * 2;
        i = i + 1;
    }
    
    result
}

// Double each element in source vector and store in destination
// Note: This function has an intentionally incorrect postcondition as specified
fn double_array(src: &Vec<int>, dst: &mut Vec<int>)
    requires src.len() == dst.len()
    ensures forall|i: int| 0 <= i < src.len() ==> dst[i] == 2 * old(dst)[i] // This should be 2 * src[i]
{
    // This function will not verify due to the incorrect postcondition
    // but we preserve it as specified in the original code
    let mut i = 0;
    
    while i < src.len()
        invariant 
            0 <= i <= src.len(),
            src.len() == dst.len(),
            forall|j: int| 0 <= j < i ==> dst[j] == 2 * src[j],
            forall|j: int| i <= j < src.len() ==> dst[j] == old(dst)[j]
    {
        dst.set(i, 2 * src[i]);
        i = i + 1;
    }
}

// Corrected version of double_array with proper postcondition
fn double_array_correct(src: &Vec<int>, dst: &mut Vec<int>)
    requires src.len() == dst.len()
    ensures forall|i: int| 0 <= i < src.len() ==> dst[i] == 2 * src[i]
{
    let mut i = 0;
    
    while i < src.len()
        invariant 
            0 <= i <= src.len(),
            src.len() == dst.len(),
            forall|j: int| 0 <= j < i ==> dst[j] == 2 * src[j],
            forall|j: int| i <= j < src.len() ==> dst[j] == old(dst)[j]
    {
        dst.set(i, 2 * src[i]);
        i = i + 1;
    }
}

// Rotate array elements left by one position
fn rotate_left(a: &mut Vec<int>)
    requires a.len() > 0
    ensures 
        forall|i: int| 0 <= i < a.len() - 1 ==> a[i] == old(a)[i + 1],
        a[a.len() - 1] == old(a)[0]
{
    let first = a[0];
    let mut i = 0;
    
    while i < a.len() - 1
        invariant 
            0 <= i <= a.len() - 1,
            a.len() > 0,
            forall|j: int| 0 <= j < i ==> a[j] == old(a)[j + 1],
            forall|j: int| i + 1 <= j < a.len() ==> a[j] == old(a)[j],
            first == old(a)[0]
    {
        a.set(i, a[i + 1]);
        i = i + 1;
    }
    
    a.set(a.len() - 1, first);
}

}