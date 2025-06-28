use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Function to find maximum element in a vector
fn Max(a: Vec<i32>) -> (m: i32)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> a[i] <= m
    ensures exists|i: int| 0 <= i < a.len() && m == a[i]
{
    let mut m = a[0];
    let mut idx = 1;  // Start from 1 since we already have a[0]
    
    while idx < a.len()
        invariant 1 <= idx <= a.len()
        invariant forall|i: int| 0 <= i < idx ==> a[i] <= m
        invariant exists|i: int| 0 <= i < idx && m == a[i]
        invariant m == a[0] || exists|j: int| 1 <= j < idx && m == a[j]
    {
        if a[idx as int] > m {
            m = a[idx as int];
        }
        idx += 1;
    }
    m
}

// Function to compute cube of a number
fn Cube(n: u32) -> (c: u32) 
    requires n <= 1625  // Ensure no overflow: 1625^3 < 2^32
    ensures c == n * n * n
{
    n * n * n
}

// Spec function for power computation
spec fn Power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * Power((n - 1) as nat) }
}

// Function to compute power of 2
fn ComputePower(N: u32) -> (y: u32) 
    requires N <= 31  // Ensure no overflow: 2^31 < 2^32
    ensures y == Power(N as nat)
{
    let mut result = 1u32;
    let mut i = 0u32;
    
    while i < N
        invariant 0 <= i <= N
        invariant result == Power(i as nat)
    {
        result = result * 2;
        i += 1;
        
        // Proof assertion to help verification
        assert(Power((i as nat)) == 2 * Power(((i - 1) as nat)));
    }
    result
}

// Function to double all elements in a vector
fn DoubleArray(src: &Vec<i32>) -> (dst: Vec<i32>)
    requires src.len() > 0
    ensures dst.len() == src.len()
    ensures forall|i: int| 0 <= i < src.len() ==> dst[i] == 2 * src[i]
{
    let mut dst = Vec::new();
    let mut idx = 0;
    
    while idx < src.len()
        invariant 0 <= idx <= src.len()
        invariant dst.len() == idx
        invariant forall|i: int| 0 <= i < idx ==> dst[i] == 2 * src[i]
    {
        dst.push(2 * src[idx as int]);
        idx += 1;
    }
    
    // Final assertion to help verification
    assert(dst.len() == src.len());
    dst
}

// Function to copy elements from one vector to another
fn CopyVector(src: &Vec<i32>) -> (dst: Vec<i32>)
    ensures dst.len() == src.len()
    ensures forall|i: int| 0 <= i < src.len() ==> dst[i] == src[i]
{
    let mut dst = Vec::new();
    let mut idx = 0;
    
    while idx < src.len()
        invariant 0 <= idx <= src.len()
        invariant dst.len() == idx
        invariant forall|i: int| 0 <= i < idx ==> dst[i] == src[i]
    {
        dst.push(src[idx as int]);
        idx += 1;
    }
    
    // Final assertion to help verification
    assert(dst.len() == src.len());
    dst
}

}