// <vc-helpers>
lemma SmallestEvenCorrectness(nodes: seq<int>, minEven: int, minIndex: int)
  requires forall i :: 0 <= i < |nodes| ==> nodes[i] >= 0
  requires 0 <= minIndex < |nodes|
  requires nodes[minIndex] == minEven
  requires minEven % 2 == 0
  requires forall i :: 0 <= i < |nodes| && nodes[i] % 2 == 0 ==> minEven <= nodes[i]
  requires forall i :: 0 <= i < minIndex ==> nodes[i] % 2 != 0 || nodes[i] > minEven
  ensures forall i :: 0 <= i < minIndex ==> nodes[i] % 2 != 0 || nodes[i] > minEven
{
}

lemma NoEvenExists(nodes: seq<int>)
  requires forall i :: 0 <= i < |nodes| ==> nodes[i] >= 0
  requires forall i :: 0 <= i < |nodes| ==> nodes[i] % 2 != 0
  ensures forall i :: 0 <= i < |nodes| ==> nodes[i] % 2 != 0
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
  var foundEven := false;
  
  var i := 0;
  while i < |nodes|
    invariant 0 <= i <= |nodes|
    invariant foundEven ==> 0 <= minIndex < i && nodes[minIndex] == minEven
    invariant foundEven ==> minEven % 2 == 0
    invariant foundEven ==> forall j :: 0 <= j < i && nodes[j] % 2 == 0 ==> minEven <= nodes[j]
    invariant foundEven ==> forall j :: 0 <= j < minIndex ==> nodes[j] % 2 != 0 || nodes[j] > minEven
    invariant !foundEven ==> forall j :: 0 <= j < i ==> nodes[j] % 2 != 0
  {
    if nodes[i] % 2 == 0 {
      if !foundEven || nodes[i] < minEven {
        minEven := nodes[i];
        minIndex := i;
        foundEven := true;
      }
    }
    i := i + 1;
  }
  
  if foundEven {
    result := [minEven, minIndex];
  } else {
    result := [];
  }
}
// </vc-code>
