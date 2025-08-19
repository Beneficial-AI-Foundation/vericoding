// SPEC

// As a second example, we add the first n odd numbers 
// This yields n*n, i.e.
//
//   1 + 3 + 5 + 7 + 9 + 11 + ... 2n+1 == n*n
//
// Here is the proof using Dafny:

method sumOdds(n:nat) returns (sum:nat)
ensures sum == n*n
{
}
