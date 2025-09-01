

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
  var result_arr := new int[|l|];
  for i := 0 to |l| - 1
    invariant 0 <= i <= |l|
    invariant forall k :: 0 <= k < i ==> result_arr[k] == l[k] + 1
  {
    result_arr[i] := l[i] + 1;
  }
  return result_arr[..]; // Convert array to sequence for return
}
// </vc-code>

