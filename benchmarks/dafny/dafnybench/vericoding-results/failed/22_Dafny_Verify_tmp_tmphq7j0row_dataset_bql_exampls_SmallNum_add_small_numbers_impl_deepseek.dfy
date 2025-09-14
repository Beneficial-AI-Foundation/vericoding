

// <vc-helpers>
function sum(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + sum(s[1..])
}

lemma SumBound(a: seq<int>, n: int, max: int)
  requires n >= 0
  requires n <= |a|
  requires forall i: int :: 0 <= i && i < n ==> a[i] <= max
  ensures sum(a[0..n]) <= max * n
{
  if n == 0 {
    assert a[0..0] == [];
    assert sum([]) == 0;
    assert max * 0 == 0;
  } else if n == 1 {
    assert a[0..1] == [a[0]];
    assert sum([a[0]]) == a[0];
    assert a[0] <= max;
    assert sum([a[0]]) <= max;
    assert max * 1 == max;
  } else {
    SumBound(a, n-1, max);
    assert a[0..n] == a[0..n-1] + [a[n-1]];
    assert sum(a[0..n]) == sum(a[0..n-1]) + a[n-1];
    assert sum(a[0..n-1]) <= max * (n-1);
    assert a[n-1] <= max;
    assert sum(a[0..n-1]) + a[n-1] <= max * (n-1) + max;
    assert max * (n-1) + max == max * n;
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
    requires n > 0;
    requires n <= a.Length;
    requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
    ensures r <= max * n;
// </vc-spec>
// <vc-code>
{
  var sum := 0;
  var i := 0;
  var s := a[..];
  
  while i < n
    invariant 0 <= i <= n
    invariant sum <= max * i
    invariant sum == sum(s[0..i])
  {
    assert a[i] <= max;
    assert s[0..i] + [s[i]] == s[0..i+1];
    sum := sum + a[i];
    i := i + 1;
  }
  
  SumBound(s, n, max);
  r := sum;
}
// </vc-code>

