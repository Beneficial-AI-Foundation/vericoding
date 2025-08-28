//Given two arrays of integers, it returns a single array with all integers merged. 
// [1,5,2,3],[4,3,5]->[1,5,2,3,4,3,5]

// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method single(x:array<int>, y:array<int>) returns (b:array<int>) 
requires x.Length > 0
requires y.Length > 0
// ensuring that the new array is the two arrays joined
ensures b[..] == x[..] + y[..]
// </vc-spec>
// </vc-spec>

// <vc-code>
method Single(x: array<int>, y: array<int>) returns (b: array<int>)
  requires x.Length > 0
  requires y.Length > 0
  ensures b[..] == x[..] + y[..]
{
  b := new int[x.Length + y.Length];
  var i := 0;
  
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant b[..i] == x[..i]
  {
    b[i] := x[i];
    i := i + 1;
  }
  
  var j := 0;
  while j < y.Length
    invariant 0 <= j <= y.Length
    invariant i == x.Length
    invariant b[..x.Length] == x[..]
    invariant b[x.Length .. x.Length + j] == y[..j]
  {
    b[i + j] := y[j];
    j := j + 1;
  }
}
// </vc-code>
