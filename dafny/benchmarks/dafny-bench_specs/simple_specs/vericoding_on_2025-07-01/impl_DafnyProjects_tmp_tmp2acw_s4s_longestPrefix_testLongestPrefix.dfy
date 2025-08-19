//ATOM

// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 
method longestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
 ensures i <= a.Length && i <= b.Length
 ensures a[..i] == b[..i]
 ensures i < a.Length && i < b.Length ==> a[i] != b[i]
{
  i := 0;
  assume i <= a.Length && i <= b.Length;
  assume a[..i] ==> b[..i];
  assume i < a.Length && i < b.Length ==> a[i] != b[i];
  return i;
}


// SPEC
 
// Test method with an example.
method testLongestPrefix() {
}