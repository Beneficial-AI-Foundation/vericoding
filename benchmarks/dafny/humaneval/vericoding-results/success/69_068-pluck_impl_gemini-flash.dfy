// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PluckSmallestEven(nodes: seq<int>) returns (result: seq<int>)

  requires |nodes| <= 10000
  requires forall i :: 0 <= i < |nodes| ==> nodes[i] >= 0

  ensures |result| == 0 || |result| == 2
  ensures |result| == 2 ==> 0 <= result[1] < |nodes| && nodes[result[1]] == result[0]
  ensures |result| == 2 ==> result[0] % 2 == 0
  ensures |result| == 2 ==> forall i :: 0 <= i < |nodes| && nodes[i] % 2 == 0 ==> result[0] <= nodes[i]
  ensures |result| == 2 ==> forall i :: 0 <= i < result[1] ==> nodes[i] % 2 != 0 || nodes[i] > result[0]
  ensures |result| == 0 ==> forall i :: 0 <= i < |nodes| ==> nodes[i] % 2 != 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix for loop bounds and postcondition relating to `result[1]` */
{
  var smallestEvenValue := -1;
  var smallestEvenIndex := -1;

  for i := 0 to |nodes|
    invariant 0 <= i <= |nodes|
    invariant smallestEvenValue == -1 ==> (forall k :: 0 <= k < i ==> nodes[k] % 2 != 0)
    invariant smallestEvenValue != -1 ==> (smallestEvenValue % 2 == 0)
    invariant smallestEvenValue != -1 ==> (0 <= smallestEvenIndex < i)
    invariant smallestEvenValue != -1 ==> (nodes[smallestEvenIndex] == smallestEvenValue)
    invariant smallestEvenValue != -1 ==> (forall k :: 0 <= k < i && nodes[k] % 2 == 0 ==> smallestEvenValue <= nodes[k])
    invariant smallestEvenValue != -1 ==> (forall k :: 0 <= k < smallestEvenIndex ==> nodes[k] % 2 != 0 || nodes[k] > smallestEvenValue)
  {
    if i < |nodes| && nodes[i] % 2 == 0 {
      if smallestEvenValue == -1 || nodes[i] < smallestEvenValue {
        smallestEvenValue := nodes[i];
        smallestEvenIndex := i;
      }
    }
  }

  if smallestEvenValue != -1 {
    result := [smallestEvenValue, smallestEvenIndex];
  } else {
    result := [];
  }
}
// </vc-code>
