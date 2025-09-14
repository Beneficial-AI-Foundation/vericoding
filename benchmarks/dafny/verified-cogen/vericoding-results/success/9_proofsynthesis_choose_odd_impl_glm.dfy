// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsOdd(x: int): bool { x % 2 == 1 }
// </vc-helpers>

// <vc-spec>
method ChooseOdd(v: array<int>) returns (odd_index: int)
    requires exists q :: 0 <= q < v.Length && v[q] % 2 == 1
    ensures 0 <= odd_index < v.Length
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant forall j :: 0 <= j < i ==> v[j] % 2 == 0
    {
        if IsOdd(v[i]) {
            odd_index := i;
            return;
        }
        i := i + 1;
    }
    // This line should never be reached due to the precondition
    odd_index := 0;
}
// </vc-code>
