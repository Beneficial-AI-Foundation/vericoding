

// <vc-helpers>
// No additional helpers needed
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
  var min_even: int := -1;
  var index_of_min: int := -1;
  var found := false;
  var i := 0;
  while i < |nodes|
    invariant 0 <= i <= |nodes|
    invariant found ==> (0 <= index_of_min < i && nodes[index_of_min] % 2 == 0 && nodes[index_of_min] == min_even)
    invariant found ==> (forall j :: 0 <= j < i && nodes[j] % 2 == 0 ==> min_even <= nodes[j])
    invariant found ==> (min_even >= 0 && min_even % 2 == 0)
    invariant found ==> forall j :: 0 <= j < index_of_min ==> nodes[j] % 2 != 0 || nodes[j] > min_even
    invariant !found ==> forall j :: 0 <= j < i ==> nodes[j] % 2 != 0
  {
    if nodes[i] % 2 == 0 {
      if !found {
        min_even := nodes[i];
        index_of_min := i;
        found := true;
      } else {
        if nodes[i] < min_even {
          min_even := nodes[i];
          index_of_min := i;
        } else if nodes[i] == min_even && i < index_of_min {
          index_of_min := i;
        }
      }
    }
    i := i + 1;
  }
  if found {
    result := [min_even, index_of_min];
  } else {
    result := [];
  }
}
// </vc-code>

