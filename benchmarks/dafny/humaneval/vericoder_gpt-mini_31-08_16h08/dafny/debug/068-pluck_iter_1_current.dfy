

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method PluckSmallestEven(nodes: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |nodes| <= 10000
  requires forall i :: 0 <= i < |nodes| ==> nodes[i] >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == 0 || |result| == 2
  ensures |result| == 2 ==> 0 <= result[1] < |nodes| && nodes[result[1]] == result[0]
  ensures |result| == 2 ==> result[0] % 2 == 0
  ensures |result| == 2 ==> forall i :: 0 <= i < |nodes| && nodes[i] % 2 == 0 ==> result[0] <= nodes[i]
  ensures |result| == 2 ==> forall i :: 0 <= i < result[1] ==> nodes[i] % 2 != 0 || nodes[i] > result[0]
  ensures |result| == 0 ==> forall i :: 0 <= i < |nodes| ==> nodes[i] % 2 != 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var found := false;
  var minVal := 0;
  var minIdx := 0;
  while i < |nodes|
    invariant 0 <= i <= |nodes|
    invariant found ==> 0 <= minIdx < i && nodes[minIdx] == minVal && minVal % 2 == 0
    invariant found ==> forall k :: 0 <= k < i && nodes[k] % 2 == 0 ==> minVal <= nodes[k]
    invariant found ==> forall k :: 0 <= k < minIdx ==> nodes[k] % 2 != 0 || nodes[k] > minVal
    invariant !found ==> forall k :: 0 <= k < i ==> nodes[k] % 2 != 0
  {
    if nodes[i] % 2 == 0 {
      if !found || nodes[i] < minVal {
        minVal := nodes[i];
        minIdx := i;
        found := true;
      }
    }
    i := i + 1;
  }
  if found {
    result := [minVal, minIdx];
  } else {
    result := [];
  }
}
// </vc-code>

