use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn random(a: int, b: int) -> (r: int)
    requires a <= b
    ensures a <= r <= b
{
    // Since we can't actually generate random numbers in a verified context,
    // we'll return a deterministic value that satisfies the postcondition
    a
}

// Helper function to create a new vector from an existing one
// Using i32 as a concrete type instead of generic T for verification
fn get_all_shuffled_data_entries(data_entries: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == data_entries.len()
{
    // For now, return a copy of the original vector
    // A real implementation would shuffle the elements
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < data_entries.len()
        invariant 
            0 <= i <= data_entries.len(),
            result.len() == i
    {
        result.push(data_entries[i]);
        i = i + 1;
    }
    
    result
}

// Alternative implementation using array-like structure
// Using i32 as a concrete type instead of generic T for verification
fn shuffle_array_data(data_entries: &Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == data_entries.len()
{
    // Simple implementation that creates a copy
    // In a real shuffle, you'd permute the elements randomly
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < data_entries.len()
        invariant 
            0 <= i <= data_entries.len(),
            result.len() == i
    {
        result.push(data_entries[i]);
        i = i + 1;
    }
    
    result
}

// Spec function for vector copying
spec fn vec_has_same_length<T>(original: Vec<T>, copy: Vec<T>) -> bool {
    original.len() == copy.len()
}

// Generic version that creates a new vector with same elements
fn get_all_shuffled_data_entries_generic<T>(data_entries: Vec<T>) -> (result: Vec<T>)
    ensures 
        result.len() == data_entries.len()
    where 
        T: Clone
{
    // Return the original vector (satisfies the length constraint)
    // In a real implementation, this would shuffle the elements
    data_entries
}

fn shuffle_array_data_generic<T>(data_entries: &Vec<T>) -> (result: Vec<T>)
    ensures 
        result.len() == data_entries.len()
    where
        T: Clone
{
    // Clone the input vector to create a new one with same length
    // In a real implementation, this would shuffle the elements
    data_entries.clone()
}

}