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
  var nx := x.Length;
  var ny := y.Length;
  b := new int[nx + ny];

  var i := 0;
  while i < nx
    invariant 0 <= i <= nx
    invariant b.Length == nx + ny
    invariant forall k :: 0 <= k < i ==> b[k] == x[k]
  {
    b[i] := x[i];
    i := i + 1;
  }

  i := 0;
  while i < ny
    invariant 0 <= i <= ny
    invariant b.Length == nx + ny
    invariant forall k :: 0 <= k < nx ==> b[k] == x[k]
    invariant forall k :: 0 <= k < i ==> b[nx + k] == y[k]
  {
    b[nx + i] := y[i];
    i := i + 1;
  }

  assert |b[..]| == |x[..] + y[..]|;
  assert forall k :: 0 <= k < b.Length ==> b[..][k] == (x[..] + y[..])[k];
  forall k | 0 <= k < b.Length
    ensures b[..][k] == (x[..] + y[..])[k]
  {
    if k < nx {
      assert b[k] == x[k];
      assert (x[..] + y[..])[k] == x[..][k];
    } else {
      var kk := k - nx;
      assert 0 <= kk;
      assert k < nx + ny;
      assert kk < ny;
      assert b[nx + kk] == y[kk];
      assert (x[..] + y[..])[k] == y[..][kk];
    }
  }
  assert b[..] == x[..] + y[..];
}
// </vc-code>

