

// <vc-helpers>
lemma min_even_unique(s: seq<int>, min_val: int)
  requires exists i :: 0 <= i < |s| && s[i] == min_val && s[i] % 2 == 0
  ensures exists k :: 0 <= k < |s| && s[k] == min_val && s[k] % 2 == 0 && (forall i :: 0 <= i < k ==> s[i] % 2 != 0 || s[i] > min_val)
{
  var k := -1;
  var found := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant (found ==> 0 <= k < i && s[k] == min_val && s[k] % 2 == 0)
    invariant (forall j :: 0 <= j < i && s[j] % 2 == 0 && s[j] < min_val ==> false)
    invariant (forall j :: 0 <= j < i && s[j] % 2 == 0 && s[j] == min_val ==> (k != -1 && k <= j) || k == -1)
  {
    if !found && i < |s| && s[i] == min_val && s[i] % 2 == 0 {
      k := i;
      found := true;
    }
  }
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
  var smallestEvenValue := -1;
  var smallestEvenIndex := -1;

  var foundEven := false;

  for i := 0 to |nodes|
    invariant 0 <= i <= |nodes|
    invariant (smallestEvenValue == -1 && smallestEvenIndex == -1 && !foundEven) ||
              (smallestEvenValue >= 0 && smallestEvenIndex >= 0 && foundEven &&
               smallestEvenValue % 2 == 0 &&
               smallestEvenValue == nodes[smallestEvenIndex] &&
               (forall k :: 0 <= k < i && nodes[k]%2 == 0 ==> nodes[k] >= smallestEvenValue))
  {
    if i < |nodes| && nodes[i] % 2 == 0 {
      if !foundEven {
        smallestEvenValue := nodes[i];
        smallestEvenIndex := i;
        foundEven := true;
      } else if nodes[i] < smallestEvenValue {
        smallestEvenValue := nodes[i];
        smallestEvenIndex := i;
      }
    }
  }

  if foundEven {
    min_even_unique(nodes, smallestEvenValue);
    var firstOccurenceIndex : int := -1;
    for i := 0 to |nodes|
      invariant 0 <= i <= |nodes|
      invariant (firstOccurenceIndex == -1 &&
                 (forall k :: 0 <= k < i ==> nodes[k] % 2 != 0 || nodes[k] > smallestEvenValue)) ||
                (firstOccurenceIndex != -1 && nodes[firstOccurenceIndex] == smallestEvenValue &&
                 nodes[firstOccurenceIndex] % 2 == 0 && firstOccurenceIndex < i &&
                 (forall k :: 0 <= k < firstOccurenceIndex ==> nodes[k] % 2 != 0 || nodes[k] > smallestEvenValue))
    {
      if i < |nodes| && nodes[i] == smallestEvenValue && nodes[i] % 2 == 0 {
        firstOccurenceIndex := i;
        break;
      }
    }
    return [smallestEvenValue, firstOccurenceIndex];
  } else {
    return [];
  }
}
// </vc-code>

