//ATOM
function isMax(m: int, numbers: seq<int>): bool
{
  m in numbers &&
  forall i :: 0 <= i < |numbers| ==> numbers[i] <= m
}

//IMPL 
method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
{
  result := [numbers[0]];
  
  var j := 1;
  while j < |numbers|
    invariant 1 <= j <= |numbers|
    invariant |result| == j
    invariant forall k :: 0 < k < j ==> isMax(result[k], numbers[0..(k+1)])
  {
    var max_so_far := numbers[0];
    var k := 1;
    while k <= j
      invariant 1 <= k <= j + 1
      invariant max_so_far in numbers[0..(j+1)]
      invariant forall l :: 0 <= l < k ==> numbers[l] <= max_so_far
    {
      if numbers[k] > max_so_far {
        max_so_far := numbers[k];
      }
      k := k + 1;
    }
    
    result := result + [max_so_far];
    j := j + 1;
  }
}