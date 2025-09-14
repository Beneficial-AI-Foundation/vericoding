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
/* helper modified by LLM (iteration 2): simple indicator for a single element less-than count */
function LessThanCountOfOne(x: int, threshold: int): nat { if x < threshold then 1 else 0 }
// </vc-helpers>

// <vc-spec>
method CountLessThan(numbers: array<int>, threshold: int) returns (result: nat)
    ensures result == CountLessThanSpec(numbers[..], threshold)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): loop iterates backwards and maintains spec-based invariant without redundant null check */
  var n := numbers.Length;
  var i: nat := n;
  result := 0;
  while i > 0
    invariant i <= numbers.Length
    invariant result == CountLessThanSpec(numbers[i..], threshold)
    decreases i
  {
    if numbers[i - 1] < threshold {
      result := result + 1;
    }
    i := i - 1;
  }
}
// </vc-code>
