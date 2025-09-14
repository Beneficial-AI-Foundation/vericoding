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
  /* code modified by LLM (iteration 5): fixed compilation error by adding semicolons after var declarations */
  var uniqueSet: set<int> := {};
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall x :: x in uniqueSet ==> CountFrequencyRcr(arr[..], x) == 1
  {
    if arr[i] !in uniqueSet && CountFrequencyRcr(arr[..], arr[i]) == 1 {
      uniqueSet := uniqueSet + {arr[i]};
    }
    i := i + 1;
  }
  unique_arr := new int[|uniqueSet|];
  var idx := 0;
  var tempSet := uniqueSet;
  while tempSet != {}
    invariant 0 <= idx <= unique_arr.Length
    invariant idx == unique_arr.Length - |tempSet|
    invariant forall k :: 0 <= k < idx ==> CountFrequencyRcr(arr[..], unique_arr[k]) == 1
  {
    var x :| x in tempSet;
    unique_arr[idx] := x;
    idx := idx + 1;
    tempSet := tempSet - {x};
  }
}
// </vc-code>
