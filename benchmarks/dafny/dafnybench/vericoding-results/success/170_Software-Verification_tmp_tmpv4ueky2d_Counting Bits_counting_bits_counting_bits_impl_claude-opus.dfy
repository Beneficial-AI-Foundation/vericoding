

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
    result := new int[n + 1];
    if n >= 0 {
        result[0] := 0;
    }
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant forall j :: 1 <= j < i ==> result[j] == result[j / 2] + j % 2
        invariant result.Length == n + 1
    {
        result[i] := result[i / 2] + i % 2;
        i := i + 1;
    }
}
// </vc-code>

