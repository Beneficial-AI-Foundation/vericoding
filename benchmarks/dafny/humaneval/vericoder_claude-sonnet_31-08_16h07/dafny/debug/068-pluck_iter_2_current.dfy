

// <vc-helpers>
lemma ForallEvenImpliesMinEven(nodes: seq<int>, minVal: int, minIdx: int)
  requires 0 <= minIdx < |nodes|
  requires nodes[minIdx] == minVal
  requires minVal % 2 == 0
  requires forall i :: 0 <= i < |nodes| && nodes[i] % 2 == 0 ==> minVal <= nodes[i]
  requires forall i :: 0 <= i < minIdx ==> nodes[i] % 2 != 0 || nodes[i] > minVal
  ensures forall i :: 0 <= i < minIdx ==> nodes[i] % 2 != 0 || nodes[i] > minVal
{
}
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
  var minEven := -1;
  var minIndex := -1;
  var hasEven := false;
  
  for i := 0 to |nodes|
    invariant 0 <= i <= |nodes|
    invariant hasEven <==> (minEven != -1 && minIndex != -1)
    invariant hasEven ==> 0 <= minIndex < i
    invariant hasEven ==> nodes[minIndex] == minEven
    invariant hasEven ==> minEven % 2 == 0
    invariant hasEven ==> forall j :: 0 <= j < i && nodes[j] % 2 == 0 ==> minEven <= nodes[j]
    invariant hasEven ==> forall j :: 0 <= j < minIndex ==> nodes[j] % 2 != 0 || nodes[j] > minEven
    invariant !hasEven ==> forall j :: 0 <= j < i ==> nodes[j] % 2 != 0
  {
    if nodes[i] % 2 == 0 {
      if !hasEven || nodes[i] < minEven || (nodes[i] == minEven && i < minIndex) {
        minEven := nodes[i];
        minIndex := i;
        hasEven := true;
      }
    }
  }
  
  if hasEven {
    ForallEvenImpliesMinEven(nodes, minEven, minIndex);
    result := [minEven, minIndex];
  } else {
    result := [];
  }
}
// </vc-code>

