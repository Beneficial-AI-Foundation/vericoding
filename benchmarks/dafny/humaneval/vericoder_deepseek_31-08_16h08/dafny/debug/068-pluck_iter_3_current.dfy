

// <vc-helpers>
predicate isEven(x: int) {
  x % 2 == 0
}

lemma EvenMinLemma(nodes: seq<int>, minIdx: int, minVal: int)
  requires 0 <= minIdx < |nodes|
  requires nodes[minIdx] == minVal
  requires isEven(minVal)
  requires forall i :: 0 <= i < |nodes| && isEven(nodes[i]) ==> minVal <= nodes[i]
  ensures forall i :: 0 <= i < minIdx ==> !isEven(nodes[i]) || nodes[i] > minVal
{
  var j := 0;
  while j < minIdx
    invariant 0 <= j <= minIdx
    invariant forall k :: 0 <= k < j ==> !isEven(nodes[k]) || nodes[k] > minVal
  {
    if isEven(nodes[j]) {
      assert nodes[j] >= minVal;
      if nodes[j] == minVal {
        assert j != minIdx;
      }
    }
    j := j + 1;
  }
}
// </vc-helpers>
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
  if |nodes| == 0 {
    result := [];
    return;
  }
  
  var minEvenValue := -1;
  var minEvenIndex := -1;
  var i := 0;
  
  while i < |nodes|
    invariant 0 <= i <= |nodes|
    invariant minEvenIndex == -1 ==> minEvenValue == -1
    invariant minEvenIndex != -1 ==> 0 <= minEvenIndex < i
    invariant minEvenIndex != -1 ==> nodes[minEvenIndex] == minEvenValue
    invariant minEvenIndex != -1 ==> minEvenValue % 2 == 0
    invariant minEvenIndex != -1 ==> forall j :: 0 <= j < i && isEven(nodes[j]) ==> minEvenValue <= nodes[j]
    invariant minEvenIndex != -1 ==> forall j :: 0 <= j < minEvenIndex ==> !isEven(nodes[j]) || nodes[j] > minEvenValue
    invariant minEvenIndex == -1 ==> forall j :: 0 <= j < i ==> !isEven(nodes[j])
  {
    if isEven(nodes[i]) {
      if minEvenIndex == -1 || nodes[i] < minEvenValue {
        minEvenValue := nodes[i];
        minEvenIndex := i;
      }
    } else if minEvenIndex == -1 {
      // Maintain invariant that no even numbers found yet
    }
    i := i + 1;
  }
  
  if minEvenIndex == -1 {
    result := [];
  } else {
    result := [minEvenValue, minEvenIndex];
    EvenMinLemma(nodes, minEvenIndex, minEvenValue);
  }
}
// </vc-code>

