// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function XorBits(x: char, y: char): char
    requires x == '0' || x == '1'
    requires y == '0' || y == '1'
    ensures XorBits(x, y) == '0' || XorBits(x, y) == '1'
    ensures XorBits(x, y) == (if x == y then '0' else '1')
{
    if x == y then '0' else '1'
}
// </vc-helpers>

// <vc-spec>
method StringXor(a: array<char>, b: array<char>) returns (result: array<char>)
    requires a.Length == b.Length
    requires forall i :: 0 <= i < a.Length ==> a[i] == '0' || a[i] == '1'
    requires forall i :: 0 <= i < b.Length ==> b[i] == '0' || b[i] == '1'
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> (result[i] == '0' || result[i] == '1')
    ensures forall i :: 0 <= i < result.Length ==> result[i] == (if a[i] == b[i] then '0' else '1')
// </vc-spec>
// <vc-code>
{
    result := new char[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result.Length == a.Length
        invariant forall j :: 0 <= j < i ==> result[j] == '0' || result[j] == '1'
        invariant forall j :: 0 <= j < i ==> result[j] == (if a[j] == b[j] then '0' else '1')
    {
        result[i] := XorBits(a[i], b[i]);
        i := i + 1;
    }
}
// </vc-code>
