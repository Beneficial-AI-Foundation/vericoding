// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function signOf(x: int): int
{
    if x > 0 then 1 else if x < 0 then -1 else 0
}
// </vc-helpers>

// <vc-spec>
method Sign(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length
    ensures
        forall i :: 0 <= i < a.Length ==> (
            (a[i] > 0 ==> result[i] == 1) &&
            (a[i] == 0 ==> result[i] == 0) &&
            (a[i] < 0 ==> result[i] == -1)
        )
// </vc-spec>
// <vc-code>
{
    result := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> result[j] == signOf(a[j])
    {
        result[i] := signOf(a[i]);
        i := i + 1;
    }
}
// </vc-code>
