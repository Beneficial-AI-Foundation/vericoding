//Given two arrays of integers, it returns a single array with all integers merged. 
// [1,5,2,3],[4,3,5]->[1,5,2,3,4,3,5]

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method single(x:array<int>, y:array<int>) returns (b:array<int>) 
requires x.Length > 0
requires y.Length > 0
// ensuring that the new array is the two arrays joined
ensures b[..] == x[..] + y[..]
// </vc-spec>
// <vc-code>
{
  var n := x.Length;
  var m := y.Length;
  b := new int[n + m];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> b[j] == x[j]
  {
    b[i] := x[i];
    i := i + 1;
  }
  i := n;
  while i < n + m
    invariant n <= i <= n + m
    invariant forall j :: 0 <= j < n ==> b[j] == x[j]
    invariant forall j :: n <= j < i ==> b[j] == y[j - n]
  {
    b[i] := y[i - n];
    i := i + 1;
  }
}
// </vc-code>

