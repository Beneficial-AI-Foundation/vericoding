

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
  var bits := new int[n + 1];
  bits[0] := 0;
  var i := 1;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall j :: 0 <= j < i ==> bits[j] == (if j == 0 then 0 else bits[j / 2] + j % 2)
    invariant bits.Length == n + 1
  {
    bits[i] := bits[i / 2] + i % 2;
    i := i + 1;
  }
  result := bits;
}
// </vc-code>

