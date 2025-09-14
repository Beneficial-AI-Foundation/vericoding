// <vc-preamble>
// </vc-preamble>

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
    invariant b[..x.Length] == x[..]
    invariant b[x.Length .. x.Length + j] == y[..j]
  {
    b[x.Length + j] := y[j];
    j := j + 1;
  }
}
// </vc-code>
