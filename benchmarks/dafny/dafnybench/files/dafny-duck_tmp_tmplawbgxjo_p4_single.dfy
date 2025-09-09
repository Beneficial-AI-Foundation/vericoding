/*
//Given two arrays of integers, it returns a single array with all integers merged. 

// [1,5,2,3],[4,3,5]->[1,5,2,3,4,3,5]

// ensuring that the new array is the two arrays joined
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method single(x:array<int>, y:array<int>) returns (b:array<int>) 
requires x.Length > 0
requires y.Length > 0
ensures b[..] == x[..] + y[..]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
