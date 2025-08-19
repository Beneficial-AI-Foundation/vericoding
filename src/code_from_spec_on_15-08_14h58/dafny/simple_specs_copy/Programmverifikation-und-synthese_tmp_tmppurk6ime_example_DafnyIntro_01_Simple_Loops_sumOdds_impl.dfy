//IMPL
// As a second example, we add the first n odd numbers 
// This yields n*n, i.e.
//
//   1 + 3 + 5 + 7 + 9 + 11 + ... 2n+1 == n*n
//
// Here is the proof using Dafny:

method sumOdds(n:nat) returns (sum:nat)
ensures sum == n*n
{
    sum := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant sum == i * i
    {
        sum := sum + (2 * i + 1);
        i := i + 1;
    }
}