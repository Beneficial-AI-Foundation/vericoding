

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method incr_list(l: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var result := new int[|l|];
  for i := 0 to |l| - 1
    ensures 0 <= i + 1 <= |l|
    ensures forall k :: 0 <= k < i + 1 ==> result[k] == l[k] + 1
  {
    result[i] := l[i] + 1;
  }
  return result;
}
// </vc-code>

