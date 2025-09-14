

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method counting_bits(n: int) returns (result: array<int>)
    requires 0 <= n <= 100000
    ensures result.Length == n + 1
    ensures forall i :: 1 <= i < n + 1 ==> result[i] == result[i / 2] + i % 2
// </vc-spec>
// <vc-code>
{
  var a := new int[n + 1];
  var i := 1;
  while i <= n
    invariant 1 <= i && i <= n + 1
    invariant a.Length == n + 1
    invariant forall j :: 1 <= j < i ==> a[j] == a[j / 2] + j % 2
    decreases n - i + 1
  {
    a[i] := a[i / 2] + i % 2;
    i := i + 1;
  }
  result := a;
}
// </vc-code>

