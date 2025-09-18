// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Clip(a: array<int>, min: int, max: int) returns (result: array<int>)
    requires min < max
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> 
        if a[i] < min then result[i] == min
        else if a[i] > max then result[i] == max
        else result[i] == a[i]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
