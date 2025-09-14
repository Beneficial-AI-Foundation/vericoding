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
  var n1 := x.Length;
  var n2 := y.Length;
  b := new int[n1 + n2];
  var i := 0;
  while i < n1
    invariant 0 <= i <= n1
    invariant b.Length == n1 + n2
    invariant b[..i] == x[..i]
  {
    b[i] := x[i];
    i := i + 1;
  }
  var k := 0;
  while k < n2
    invariant 0 <= k <= n2
    invariant b.Length == n1 + n2
    invariant b[..n1 + k] == x[..] + y[..k]
  {
    b[n1 + k] := y[k];
    k := k + 1;
  }
}
// </vc-code>

