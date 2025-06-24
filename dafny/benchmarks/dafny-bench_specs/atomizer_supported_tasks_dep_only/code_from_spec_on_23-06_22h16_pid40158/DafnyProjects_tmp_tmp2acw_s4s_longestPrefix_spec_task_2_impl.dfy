// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 
//IMPL longestPrefix
method longestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
 ensures i <= a.Length && i <= b.Length
 ensures a[..i] == b[..i]
 ensures i < a.Length && i < b.Length ==> a[i] != b[i]
{
    i := 0;
    while i < a.Length && i < b.Length && a[i] == b[i]
        invariant 0 <= i <= a.Length && i <= b.Length
        invariant a[..i] == b[..i]
    {
        i := i + 1;
    }
}

 
// Test method with an example.
//IMPL testLongestPrefix
 
// Test method with an example.
method testLongestPrefix() {
    var a := new int[3];
    var b := new int[3];
    a[0] := 1; a[1] := 2; a[2] := 3;
    b[0] := 1; b[1] := 2; b[2] := 4;
    
    var result := longestPrefix(a, b);
    assert result == 2;
}