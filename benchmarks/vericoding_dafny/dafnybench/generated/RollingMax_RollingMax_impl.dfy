function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}

// <vc-helpers>
// </vc-helpers>

method RollingMax(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
// </vc-spec>
// <vc-code>
{
  result := [numbers[0]];
  var currentMax := numbers[0];
  
  var i := 1;
  while i < |numbers|
    invariant 1 <= i <= |numbers|
    invariant |result| == i
    invariant currentMax == result[i-1]
    invariant forall j :: 0 < j < i ==> isMax(result[j], numbers[0..(j+1)])
    invariant isMax(currentMax, numbers[0..i])
  {
    if numbers[i] > currentMax {
      currentMax := numbers[i];
    }
    result := result + [currentMax];
    i := i + 1;
  }
}
// </vc-code>