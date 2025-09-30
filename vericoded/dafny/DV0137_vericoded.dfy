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
/* helper modified by LLM (iteration 2): Added lemma to prove loop invariant maintenance */
lemma CountLessThanSpecAppend(s: seq<int>, threshold: int, x: int)
  ensures CountLessThanSpec(s + [x], threshold) == CountLessThanSpec(s, threshold) + (if x < threshold then 1 else 0)
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    CountLessThanSpecAppend(s[1..], threshold, x);
  }
}
// </vc-helpers>

// <vc-spec>
method CountLessThan(numbers: array<int>, threshold: int) returns (result: nat)
    ensures result == CountLessThanSpec(numbers[..], threshold)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed loop invariant by using lemma to prove maintenance */
{
  result := 0;
  var i := 0;
  while i < numbers.Length
    invariant 0 <= i <= numbers.Length
    invariant result == CountLessThanSpec(numbers[..i], threshold)
  {
    assert numbers[..i+1] == numbers[..i] + [numbers[i]];
    CountLessThanSpecAppend(numbers[..i], threshold, numbers[i]);
    if numbers[i] < threshold {
      result := result + 1;
    }
    i := i + 1;
  }
  assert numbers[..i] == numbers[..numbers.Length] == numbers[..];
}
// </vc-code>
