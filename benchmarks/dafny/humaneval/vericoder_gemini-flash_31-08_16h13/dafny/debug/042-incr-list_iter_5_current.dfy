

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
  var arr := new int[|l|];
  for i := 0 to |l| - 1
    invariant 0 <= i <= |l|
    invariant forall j :: 0 <= j < i ==> arr[j] == l[j] + 1
  {
    arr[i] := l[i] + 1;
  }
  return arr[..];
}
// </vc-code>

