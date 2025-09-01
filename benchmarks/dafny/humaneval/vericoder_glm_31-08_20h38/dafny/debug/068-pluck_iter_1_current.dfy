

// <vc-helpers>
// No helper code needed.
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
  var found := false;
  var minEven := 0;
  var idx := 0;
  for i := 0 to |nodes|
    invariant 0 <= i <= |nodes|
    invariant !found ==> forall j :: 0 <= j < i ==> nodes[j] % 2 != 0
    invariant found ==> 
        minEven % 2 == 0 && 0 <= idx < i && nodes[idx] == minEven
    invariant found ==> 
        forall j :: 0 <= j < i && nodes[j] % 2 == 0 ==> minEven <= nodes[j]
    invariant found ==> 
        forall j :: 0 <= j < idx ==> nodes[j] % 2 != 0 || nodes[j] > minEven
  {
    if nodes[i] % 2 == 0 {
      if !found {
        found := true;
        minEven := nodes[i];
        idx := i;
      } else {
        if nodes[i] < minEven {
          minEven := nodes[i];
          idx := i;
        }
      }
    }
  }
  if found {
    return [minEven, idx];
  } else {
    return [];
  }
}
// </vc-code>

