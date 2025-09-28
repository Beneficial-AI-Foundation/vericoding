// <vc-preamble>
function CountFrequencyRcr(s: seq<int>, key: int): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountFrequencyRcr(s[..|s|-1], key) + if s[|s|-1] == key then
            1
        else
            0
}
// </vc-preamble>

// <vc-helpers>
predicate IsUniqueInSeq(s: seq<int>, x: int) { CountFrequencyRcr(s, x) == 1 }

lemma CountFrequencyRcrNonNeg(s: seq<int>, key: int)
  ensures CountFrequencyRcr(s, key) >= 0
{
  if |s| == 0 {
  } else {
    CountFrequencyRcrNonNeg(s[..|s|-1], key);
  }
}
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(arr: array<int>) returns (unique_arr: array<int>)
    ensures forall i :: 0 <= i < unique_arr.Length ==> CountFrequencyRcr(arr[..], unique_arr[i]) == 1
// </vc-spec>
// <vc-code>
{
  var s: seq<int> := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < |s| ==> CountFrequencyRcr(arr[..], s[k]) == 1
  {
    if CountFrequencyRcr(arr[..], arr[i]) == 1 {
      s := s + [arr[i]];
    }
    i := i + 1;
  }
  unique_arr := new int[|s|];
  var j := 0;
  while j < |s|
    invariant 0 <= j <= |s|
    invariant forall k :: 0 <= k < j ==> unique_arr[k] == s[k] && CountFrequencyRcr(arr[..], unique_arr[k]) == 1
  {
    unique_arr[j] := s[j];
    j := j + 1;
  }
}
// </vc-code>
