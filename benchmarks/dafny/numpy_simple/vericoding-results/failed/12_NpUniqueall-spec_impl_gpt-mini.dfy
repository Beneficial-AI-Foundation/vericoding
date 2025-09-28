// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): unique sequence without duplicates */
function UniqueSeq(s: seq<int>): seq<int>
  ensures |result| <= |s|
  ensures (forall k :: 0 <= k < |s| ==> exists j :: 0 <= j < |result| && result[j] == s[k])
  ensures (forall i, j :: 0 <= i < |result| && 0 <= j < i ==> result[i] != result[j])
  decreases |s|
{
  if |s| == 0 then
    []
  else
    var head := s[0];
    var tail := UniqueSeq(s[1..]);
    if (exists j :: 0 <= j < |tail| && tail[j] == head) then tail else [head] + tail
}

// </vc-helpers>

// <vc-spec>
method UniqueAll(arr: array<int>) returns (ret: array<int>)
    ensures
        ret.Length <= arr.Length &&
        (forall i :: 0 <= i < arr.Length ==> exists j :: 0 <= j < ret.Length && ret[j] == arr[i]) &&
        (forall i, j :: 0 <= i < ret.Length && 0 <= j < i ==> ret[i] != ret[j])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): construct unique array by copying UniqueSeq */
{
  var s := UniqueSeq(arr[..]);
  ret := new int[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> ret[k] == s[k]
  {
    ret[i] := s[i];
    i := i + 1;
  }
}

// </vc-code>
