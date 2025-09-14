// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// VSComp 2010, problem 1, compute the sum and max of the elements of an array and prove
// that 'sum <= N * max'.
// Rustan Leino, 18 August 2010.
//
// The problem statement gave the pseudo-code for the method, but did not ask to prove
// that 'sum' or 'max' return as the sum and max, respectively, of the array.  The
// given assumption that the array's elements are non-negative is not needed to establish
// the requested postcondition.

// <vc-helpers>
function Max(arr: seq<int>): int
  requires arr != []
  decreases |arr|
  ensures forall k :: 0 <= k < |arr| ==> arr[k] <= Max(arr)
  ensures exists k :: 0 <= k < |arr| && arr[k] == Max(arr)
{
  if |arr| == 1 then arr[0]
  else if arr[0] >= Max(arr[1..]) then arr[0]
  else Max(arr[1..])
}

function Sum(arr: seq<int>): int
  decreases |arr|
  ensures forall x :: Sum(arr + [x]) == Sum(arr) + x
{
  if arr == [] then 0
  else arr[0] + Sum(arr[1..])
}
// </vc-helpers>

// <vc-spec>
method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k]);
  ensures sum <= N * max;
// </vc-spec>
// <vc-code>
{
  var s := 0;
  var m := -1;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant m == (if i == 0 then -1 else Max(a[..i]))
    invariant s == Sum(a[..i])
    invariant forall k :: 0 <= k < i ==> a[k] <= m
    invariant s <= i * m
  {
    if i == 0 || a[i] > m {
      m := a[i];
    }
    s := s + a[i];
    i := i + 1;
  }
  sum := s;
  max := m;
}
// </vc-code>

