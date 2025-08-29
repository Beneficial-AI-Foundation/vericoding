function dist(a: real, b: real) : (d : real)
    ensures d >= 0.0
    ensures (d == 0.0) <==> a == b
{
    if a < b then b - a else a - b
}
function des(s: seq<real>, a: int, b: int) : bool {
    // distinct elements
    0 <= a < |s| && 0 <= b < |s| && a != b
}

// <vc-helpers>
// Helper lemma to prove properties about distances
lemma DistanceProperties(a: real, b: real)
  ensures dist(a, b) >= 0.0
  ensures dist(a, b) == 0.0 <==> a == b
  ensures dist(a, b) == dist(b, a)
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def find_closest_elements(numbers: List[float]) -> Tuple[float, float]
From a supplied list of numbers (of length at least two) select and return two that are the closest to each other and return them in order (smaller number, larger number).
*/
// </vc-description>

// <vc-spec>
method FindClosestElements(numbers: seq<real>) returns (smallest: real, largest: real)
  requires |numbers| >= 2
  ensures smallest <= largest
  ensures exists i, j :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && smallest == numbers[i] && largest == numbers[j]
  ensures forall k, m :: 0 <= k < |numbers| && 0 <= m < |numbers| && k != m ==> dist(smallest, largest) <= dist(numbers[k], numbers[m])
// </vc-spec>
// <vc-code>
{
  var minDist := dist(numbers[0], numbers[1]);
  var minI, minJ := 0, 1;
  var smallestVal, largestVal := if numbers[0] <= numbers[1] then numbers[0] else numbers[1], if numbers[0] <= numbers[1] then numbers[1] else numbers[0];

  var i := 0;
  while i < |numbers| - 1
    invariant 0 <= i < |numbers|
    invariant 0 <= minI < |numbers| && 0 <= minJ < |numbers| && minI != minJ
    invariant smallestVal <= largestVal
    invariant smallestVal == numbers[minI] && largestVal == numbers[minJ]
    invariant minDist == dist(smallestVal, largestVal)
    invariant forall k, m :: 0 <= k < i && 0 <= m < |numbers| && k != m ==> minDist <= dist(numbers[k], numbers[m])
  {
    var j := i + 1;
    while j < |numbers|
      invariant 0 <= i < j <= |numbers|
      invariant 0 <= minI < |numbers| && 0 <= minJ < |numbers| && minI != minJ
      invariant smallestVal <= largestVal
      invariant smallestVal == numbers[minI] && largestVal == numbers[minJ]
      invariant minDist == dist(smallestVal, largestVal)
      invariant forall k, m :: 0 <= k < i && 0 <= m < |numbers| && k != m ==> minDist <= dist(numbers[k], numbers[m])
      invariant forall m :: i <= m < j && i != m ==> minDist <= dist(numbers[i], numbers[m])
    {
      var currDist := dist(numbers[i], numbers[j]);
      if currDist < minDist {
        minDist := currDist;
        minI := i;
        minJ := j;
        smallestVal := if numbers[i] <= numbers[j] then numbers[i] else numbers[j];
        largestVal := if numbers[i] <= numbers[j] then numbers[j] else numbers[i];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  smallest := smallestVal;
  largest := largestVal;
}
// </vc-code>
