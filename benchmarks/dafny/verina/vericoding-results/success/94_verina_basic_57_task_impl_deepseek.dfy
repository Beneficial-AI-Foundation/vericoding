// <vc-preamble>
/* Helper function to recursively count elements less than threshold */
function CountLessThanSpec(numbers: seq<int>, threshold: int): nat
    decreases |numbers|
{
    if |numbers| == 0 then
        0
    else
        var first := numbers[0];
        var rest := numbers[1..];
        if first < threshold then
            1 + CountLessThanSpec(rest, threshold)
        else
            CountLessThanSpec(rest, threshold)
}
// </vc-preamble>

// <vc-helpers>
function CountLessThanIter(numbers: array<int>, threshold: int, index: int, count: nat): (c: nat)
    requires 0 <= index <= numbers.Length
    reads numbers
    ensures c == count + CountLessThanSpec(numbers[index..], threshold)
    decreases numbers.Length - index
{
    if index == numbers.Length then
        count
    else if numbers[index] < threshold then
        CountLessThanIter(numbers, threshold, index + 1, count + 1)
    else
        CountLessThanIter(numbers, threshold, index + 1, count)
}
// </vc-helpers>

// <vc-spec>
method CountLessThan(numbers: array<int>, threshold: int) returns (result: nat)
    ensures result == CountLessThanSpec(numbers[..], threshold)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added reads annotation to helper */
  result := CountLessThanIter(numbers, threshold, 0, 0);
}
// </vc-code>
