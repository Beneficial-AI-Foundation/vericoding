// <vc-helpers>
// Helper function to count frequency of a value in a sequence
function CountFrequency(numbers: seq<int>, value: int): int
{
  if |numbers| == 0 then 0
  else if numbers[0] == value then 1 + CountFrequency(numbers[1..], value)
  else CountFrequency(numbers[1..], value)
}

// Lemma to ensure frequency count is non-negative
lemma FrequencyNonNegative(numbers: seq<int>, value: int)
  ensures CountFrequency(numbers, value) >= 0
{
  if |numbers| == 0 {
    assert CountFrequency(numbers, value) == 0;
  } else {
    FrequencyNonNegative(numbers[1..], value);
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def search(numbers: List[int]) -> int
You are given a non-empty list of positive integers. Return the greatest integer that is greater than zero, and has a frequency greater than or equal to the value of the integer itself. The frequency of an integer is the number of times it appears in the list. If no such a value exist, return -1.
*/
// </vc-description>

// <vc-spec>
method search(numbers: seq<int>) returns (result: int)
  requires |numbers| > 0
  requires forall i :: 0 <= i < |numbers| ==> numbers[i] > 0
  ensures result == -1 || (result > 0 && CountFrequency(numbers, result) >= result)
  ensures forall x :: x > 0 && CountFrequency(numbers, x) >= x ==> x <= result || result == -1
// </vc-spec>
// <vc-code>
{
  var candidates: set<int> := set x | x in numbers;
  var maxVal := -1;
  var candidateSeq: seq<int> := [];
  var sCopy := candidates;
  while sCopy != {}
    decreases |sCopy|
  {
    var x :| x in sCopy;
    candidateSeq := candidateSeq + [x];
    sCopy := sCopy - {x};
  }
  var i := 0;
  while i < |candidateSeq|
    invariant 0 <= i <= |candidateSeq|
    invariant maxVal == -1 || (maxVal in candidates && CountFrequency(numbers, maxVal) >= maxVal)
    invariant forall k :: 0 <= k < i ==> (maxVal == -1 || candidateSeq[k] <= maxVal || CountFrequency(numbers, candidateSeq[k]) < candidateSeq[k])
  {
    var val := candidateSeq[i];
    var freq := CountFrequency(numbers, val);
    if freq >= val && (maxVal == -1 || val > maxVal) {
      maxVal := val;
    }
    i := i + 1;
  }
  result := maxVal;
}
// </vc-code>
