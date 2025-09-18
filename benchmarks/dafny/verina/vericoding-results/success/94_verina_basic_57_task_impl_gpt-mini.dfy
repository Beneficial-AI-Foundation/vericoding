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
/* helper modified by LLM (iteration 2): lemma to unfold CountLessThanSpec at a suffix index */
lemma CountLessThanSpec_SuffixUnfold(s: seq<int>, i: nat, thr: int)
  requires i < |s|
  ensures CountLessThanSpec(s[i..], thr) == (if s[i] < thr then 1 + CountLessThanSpec(s[i+1..], thr) else CountLessThanSpec(s[i+1..], thr))
  decreases |s| - i
{
  var suffix := s[i..];
  assert |suffix| > 0;
  var first := suffix[0];
  var rest := suffix[1..];
  assert first == s[i];
  assert rest == s[i+1..];
  if first < thr {
    assert CountLessThanSpec(suffix, thr) == 1 + CountLessThanSpec(rest, thr);
  } else {
    assert CountLessThanSpec(suffix, thr) == CountLessThanSpec(rest, thr);
  }
}
// </vc-helpers>

// <vc-spec>
method CountLessThan(numbers: array<int>, threshold: int) returns (result: nat)
    ensures result == CountLessThanSpec(numbers[..], threshold)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate backwards and use lemma to maintain invariant */
  var i := numbers.Length;
  result := 0;
  while i > 0
    invariant 0 <= i <= numbers.Length
    invariant result == CountLessThanSpec(numbers[i..], threshold)
    decreases i
  {
    i := i - 1;
    CountLessThanSpec_SuffixUnfold(numbers[..], i, threshold);
    if numbers[i] < threshold {
      result := result + 1;
    }
  }
}
// </vc-code>
