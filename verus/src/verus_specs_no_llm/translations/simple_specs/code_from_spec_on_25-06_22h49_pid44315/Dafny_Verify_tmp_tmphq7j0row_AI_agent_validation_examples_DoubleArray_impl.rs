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
    let mut idx = 1usize;
    
    while idx < a.len()
        invariant 1 <= idx <= a.len()
        invariant forall|i: int| 0 <= i < idx ==> a[i] <= m
        invariant exists|i: int| 0 <= i < idx && m == a[i]
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
    if n == 0 { 
        1 
    } else { 
        2 * Power(n - 1)
    }
}

// Lemma to help with power computation
proof fn power_step_lemma(i: nat)
    ensures Power(i + 1) == 2 * Power(i)
{
    // The proof follows from the definition
}

// Function to compute power of 2
fn ComputePower(N: u32) -> (y: u32) 
    requires N <= 30  // More conservative bound
    ensures y == Power(N as nat)
{
    let mut result = 1u32;
    let mut i = 0u32;
    
    while i < N
        invariant 0 <= i <= N <= 30
        invariant result == Power(i as nat)
        invariant result <= u32::MAX // Ensure no overflow
    {
        proof {
            power_step_lemma(i as nat);
        }
        result = result * 2;
        i += 1;
    }
    result
}

// Function to double all elements in a vector
fn DoubleArray(src: &Vec<i32>) -> (dst: Vec<i32>)
    requires src.len() > 0
    requires forall|i: int| 0 <= i < src.len() ==> src[i] <= i32::MAX / 2 && src[i] >= i32::MIN / 2  // Prevent overflow
    ensures dst.len() == src.len()
    ensures forall|i: int| 0 <= i < src.len() ==> dst[i] == 2 * src[i]
{
    let mut dst = Vec::new();
    let mut idx = 0usize;
    
    while idx < src.len()
        invariant 0 <= idx <= src.len()
        invariant dst.len() == idx
        invariant forall|i: int| 0 <= i < idx ==> dst[i] == 2 * src[i]
    {
        let doubled_val = 2 * src[idx as int];
        dst.push(doubled_val);
        idx += 1;
    }
    
    dst
}

// Function to copy elements from one vector to another
fn CopyVector(src: &Vec<i32>) -> (dst: Vec<i32>)
    ensures dst.len() == src.len()
    ensures forall|i: int| 0 <= i < src.len() ==> dst[i] == src[i]
{
    let mut dst = Vec::new();
    let mut idx = 0usize;
    
    while idx < src.len()
        invariant 0 <= idx <= src.len()
        invariant dst.len() == idx
        invariant forall|i: int| 0 <= i < idx ==> dst[i] == src[i]
    {
        dst.push(src[idx as int]);
        idx += 1;
    }
    
    dst
}

}