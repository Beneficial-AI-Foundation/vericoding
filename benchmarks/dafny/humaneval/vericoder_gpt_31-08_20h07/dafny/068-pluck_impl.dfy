

// <vc-helpers>

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
    invariant found ==> 0 <= minIdx < i
    invariant found ==> nodes[minIdx] == minVal
    invariant found ==> minVal % 2 == 0
    invariant found ==> forall j :: 0 <= j < i && nodes[j] % 2 == 0 ==> minVal <= nodes[j]
    invariant !found ==> forall j :: 0 <= j < i ==> nodes[j] % 2 != 0
    invariant found ==> forall j :: 0 <= j < minIdx ==> nodes[j] % 2 != 0 || nodes[j] > minVal
  {
    if nodes[i] % 2 == 0 {
      if !found || nodes[i] < minVal {
        found := true;
        minVal := nodes[i];
        minIdx := i;
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

