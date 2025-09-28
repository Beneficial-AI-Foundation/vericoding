// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function subtractElement(a: int, b: int): int
{
    a - b
}

// </vc-helpers>

// <vc-spec>
method subtract(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i] - b[i]
// </vc-spec>
// <vc-code>
{
    result := new int[a.Length];
    var index := 0;
    while index < a.Length
        invariant 0 <= index <= a.Length
        invariant forall j :: 0 <= j < index ==> result[j] == a[j] - b[j]
    {
        result[index] := subtractElement(a[index], b[index]);
        index := index + 1;
    }
}
// </vc-code>
