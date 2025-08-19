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
  result := [];
  var current_max := numbers[0];
  result := result + [current_max];
  
  var j := 1;
  while j < |numbers|
    invariant 1 <= j <= |numbers|
    invariant |result| == j
    invariant forall k :: 0 < k < j ==> isMax(result[k], numbers[0..(k+1)])
    /* code modified by LLM (iteration 1): added invariant to track that current_max is the maximum of elements seen so far */
    invariant current_max in numbers[0..j]
    invariant forall k :: 0 <= k < j ==> numbers[k] <= current_max
  {
    if numbers[j] > current_max {
      current_max := numbers[j];
    }
    /* code modified by LLM (iteration 1): added assertion to help prove the loop invariant */
    assert current_max in numbers[0..(j+1)];
    assert forall k :: 0 <= k <= j ==> numbers[k] <= current_max;
    result := result + [current_max];
    /* code modified by LLM (iteration 1): added assertion to help prove isMax property */
    assert isMax(current_max, numbers[0..(j+1)]);
    j := j + 1;
  }
}