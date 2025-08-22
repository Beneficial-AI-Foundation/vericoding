// ****************************************************************************************
//                              DafnyIntro.dfy
// ****************************************************************************************
// We write a program to sum all numbers from 1 to n
// 
//  Gauss' formula states that 1 + 2 + 3 + ... + (n-1) + n == n*(n+1)/2 
//
// We take this a specification, thus in effect we use Dafny to prove Gauss' formula: 

// In essence Dafny does an inductive proof. It needs help with a loop "invariant".
// This is a condition which is 

// - true at the beginning of the loop
// - maintained with each passage through the loop body.

// These requirements correspond to an inductive proof

// - the invariant is the inductive hypothesis H(i)
// - it must be true for i=0
// - it must remain true when stepping from i to i+1,    

// Here we use two invariants I1 and I2, which amounts to the same as using I1 && I2:   

//IMPL Gauss
method Gauss(n:int) returns (sum:int)
requires n >= 0
ensures sum == n*(n+1)/2     // 
{
    sum := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant sum == i*(i+1)/2
    {
        i := i + 1;
        sum := sum + i;
    }
}


// As a second example, we add the first n odd numbers 
// This yields n*n, i.e.
//
//      1 + 3 + 5 + 7 + 9 + 11 + ... 2n+1 == n*n
//
// Here is the proof using Dafny:

//ATOM_PLACEHOLDER_sumOdds

// This verifies, so the proof is complete !!



// This verifies, so the proof is complete !!