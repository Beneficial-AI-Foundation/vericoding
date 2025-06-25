// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 
// SPEC 
// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 
pub fn longestPrefix(a: &[int], b: &[int]) -> (i: nat)
    ensures(i <= a.len() && i <= b.len())
    ensures(a[..i] == b[..i])
    ensures(i < a.len() && i < b.len() ==> a[i] != b[i])
{
}

 
// Test method with an example.
// SPEC 
 
// Test method with an example.
pub fn testLongestPrefix() {
}