// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed 'reduces (*)' as it's not needed for pure functions. */
function iota(n: int): seq<int> { if n <= 0 then [] else iota(n-1) + [n-1] }
// </vc-helpers>

// <vc-spec>
method Reverse(a: array<int>) returns (result: array<int>)
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[a.Length - 1 - i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Corrected the implementation of the Reverse method to properly reverse an array. */
{
    result := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result.Length == a.Length
        invariant forall j :: 0 <= j < i ==> result[j] == a[a.Length - 1 - j]
    {
        result[i] := a[a.Length - 1 - i];
        i := i + 1;
    }
}
// </vc-code>
