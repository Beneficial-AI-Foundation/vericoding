function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}

// <vc-helpers>
// </vc-helpers>

method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
// </vc-spec>
// <vc-code>
{
  result := [numbers[0]];
  var current_max := numbers[0];
  
  var j := 1;
  while j < |numbers|
    invariant 1 <= j <= |numbers|
    invariant |result| == j
    invariant current_max == result[j-1]
    invariant forall k :: 0 < k < j ==> isMax(result[k], numbers[0..(k+1)])
    invariant current_max in numbers[0..j]
    invariant forall k :: 0 <= k < j ==> numbers[k] <= current_max
  {
    if numbers[j] > current_max {
      current_max := numbers[j];
    }
    result := result + [current_max];
    j := j + 1;
  }
}
// </vc-code>