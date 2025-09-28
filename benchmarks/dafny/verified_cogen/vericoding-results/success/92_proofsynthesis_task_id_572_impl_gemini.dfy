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

// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(arr: array<int>) returns (unique_arr: array<int>)
    ensures forall i :: 0 <= i < unique_arr.Length ==> CountFrequencyRcr(arr[..], unique_arr[i]) == 1
// </vc-spec>
// <vc-code>
{
  var temp_seq: seq<int> := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall x :: x in temp_seq ==> CountFrequencyRcr(arr[..], x) == 1
  {
    if CountFrequencyRcr(arr[..], arr[i]) == 1 {
        if arr[i] !in temp_seq {
            temp_seq := temp_seq + [arr[i]];
        }
    }
    i := i + 1;
  }

  unique_arr := new int[|temp_seq|];
  var j := 0;
  while j < |temp_seq|
    invariant 0 <= j <= |temp_seq|
    invariant unique_arr.Length == |temp_seq|
    invariant forall x :: x in temp_seq ==> CountFrequencyRcr(arr[..], x) == 1
    invariant forall k :: 0 <= k < j ==> unique_arr[k] == temp_seq[k]
  {
    unique_arr[j] := temp_seq[j];
    j := j + 1;
  }
}
// </vc-code>
