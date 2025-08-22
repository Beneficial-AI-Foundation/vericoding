// IMPL
// ASSIGNMENT P1
// CMSC 433 FALL 2023
// PERFECT SCORE: 100 POINTS
//
// This assignment contains nine questions, each of which involves writing Dafny
// code. You should include your solutions in a single Dafny file and submit it using
// Gradescope.
//
// Revision history
//
// 2023-09-22 2:50 pm  Fixed typo in Problem 3.


// Question 1 (5 points)
//
// Fill in a requires clause that enables Dafny to verify
// method PlusOne

method PlusOne (x : int) returns (y : int)
  requires x >= 0
  ensures y > 0
{
  y := x + 1;
}