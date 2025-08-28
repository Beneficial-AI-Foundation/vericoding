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
{
  // impl-start
  var smallestEven: int := -1;
  var smallestIndex: int := -1;

  for i := 0 to |nodes|
    // invariants-start
    invariant 0 <= i <= |nodes|
    invariant smallestEven == -1 <==> smallestIndex == -1
    invariant smallestIndex != -1 ==> 0 <= smallestIndex < i
    invariant smallestIndex != -1 ==> nodes[smallestIndex] == smallestEven
    invariant smallestEven != -1 ==> smallestEven % 2 == 0
    invariant smallestEven != -1 ==> forall j :: 0 <= j < i && nodes[j] % 2 == 0 ==> smallestEven <= nodes[j]
    invariant smallestIndex != -1 ==> forall j :: 0 <= j < smallestIndex ==> nodes[j] % 2 != 0 || nodes[j] > smallestEven
    invariant smallestIndex == -1 ==> forall j :: 0 <= j < i ==> nodes[j] % 2 != 0
    // invariants-end
  {
    if nodes[i] % 2 == 0 && (smallestEven == -1 || nodes[i] < smallestEven) {
      smallestEven := nodes[i];
      smallestIndex := i;
    }
  }

  if smallestIndex == -1 {
    return [];
  } else {
    return [smallestEven, smallestIndex];
  }
  // impl-end
}
