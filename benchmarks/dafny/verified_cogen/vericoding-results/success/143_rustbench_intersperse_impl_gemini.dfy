// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Intersperse(numbers: array<int>, delim: int) returns (res: seq<int>)
    ensures
        numbers.Length == 0 ==> |res| == 0
    ensures
        numbers.Length != 0 ==> |res| == 2 * numbers.Length - 1
    ensures
        forall i :: 0 <= i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
    ensures
        forall i :: 0 <= i < |res| && i % 2 == 1 ==> res[i] == delim
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): adjusted loop to simplify invariants */
    res := [];
    var i := 0;
    while i < numbers.Length
        invariant 0 <= i <= numbers.Length
        invariant |res| == if i == 0 then 0 else 2 * i - 1
        invariant forall k :: 0 <= k < |res| && k % 2 == 0 ==> res[k] == numbers[k / 2]
        invariant forall k :: 0 <= k < |res| && k % 2 == 1 ==> res[k] == delim
    {
        if i == 0 {
            res := [numbers[0]];
        } else {
            res := res + [delim, numbers[i]];
        }
        i := i + 1;
    }

    if numbers.Length == 0 {
        res := [];
    }
}
// </vc-code>
