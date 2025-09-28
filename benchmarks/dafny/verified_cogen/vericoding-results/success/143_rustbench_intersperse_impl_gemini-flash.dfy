// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed a no-op helper */
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
    if numbers.Length == 0 {
        return [];
    }

    var result_seq: seq<int> := [];
    var j := 0;
    while j < numbers.Length
        invariant 0 <= j <= numbers.Length
        invariant |result_seq| == (if j == numbers.Length then (2 * numbers.Length - 1) else (2 * j))
        invariant forall k :: 0 <= k < |result_seq| && k % 2 == 0 ==> result_seq[k] == numbers[k / 2]
        invariant forall k :: 0 <= k < |result_seq| && k % 2 == 1 ==> result_seq[k] == delim
    {
        result_seq := result_seq + [numbers[j]];
        if j < numbers.Length - 1 {
            result_seq := result_seq + [delim];
        }
        j := j + 1;
    }
    return result_seq;
}
// </vc-code>
