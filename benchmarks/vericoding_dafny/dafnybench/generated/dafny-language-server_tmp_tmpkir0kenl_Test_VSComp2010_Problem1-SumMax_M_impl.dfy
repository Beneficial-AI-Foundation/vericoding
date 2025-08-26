function SumUpTo(a: array<int>, i: int): int
  reads a
  requires 0 <= i <= a.Length
{
  if i == 0 then 0 else SumUpTo(a, i-1) + a[i-1]
}

function MaxUpTo(a: array<int>, i: int): int
  reads a
  requires 0 < i <= a.Length
{
  if i == 1 then a[0] else if a[i-1] > MaxUpTo(a, i-1) then a[i-1] else MaxUpTo(a, i-1)
}
// </vc-helpers>

// <vc-spec>
method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k]);
  ensures sum <= N * max;
// </vc-spec>
// <vc-code>
{
  if N == 0 {
    sum := 0;
    max := 0;
    return;
  }
  
  sum := 0;
  max := a[0];
  var i := 0;
  
  while i < N
    invariant 0 <= i <= N;
    invariant sum == SumUpTo(a, i);
    invariant i > 0 ==> max >= MaxUpTo(a, i);
    invariant forall k :: 0 <= k < i ==> a[k] <= max;
    invariant sum <= i * max;
  {
    sum := sum + a[i];
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>