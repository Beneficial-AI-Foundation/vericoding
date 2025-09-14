// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsIncreasing(s: seq<int>) {
  forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

function LongestIncreasingSubsequenceLengthRecursive(numbers: seq<int>, currentIndex: int, lastNumber: int): (length: nat)
  requires 0 <= currentIndex <= |numbers|
  ensures length <= |numbers| - currentIndex
  decreases |numbers| - currentIndex
{
  if currentIndex >= |numbers| then
    0
  else
    if numbers[currentIndex] > lastNumber then
      var take := 1 + LongestIncreasingSubsequenceLengthRecursive(numbers, currentIndex + 1, numbers[currentIndex]);
      var skip := LongestIncreasingSubsequenceLengthRecursive(numbers, currentIndex + 1, lastNumber);
      max(take, skip)
    else
      LongestIncreasingSubsequenceLengthRecursive(numbers, currentIndex + 1, lastNumber)
}

function max(a: nat, b: nat): nat
{
  if a > b then a else b
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(numbers: array<int>) returns (result: nat)
    ensures result <= numbers.Length
// </vc-spec>
// <vc-code>
{
  if numbers.Length == 0 {
    result := 0;
  } else {
    result := LongestIncreasingSubsequenceLengthRecursive(numbers[..], 0, -1);
  }
}
// </vc-code>
