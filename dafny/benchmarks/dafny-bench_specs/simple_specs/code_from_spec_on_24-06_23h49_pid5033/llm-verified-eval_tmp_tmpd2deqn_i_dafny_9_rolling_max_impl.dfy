//ATOM
function isMax(m: int, numbers: seq<int>): bool
{
  m in numbers &&
  forall i :: 0 <= i < |numbers| ==> numbers[i] <= m
}

//IMPL rolling_max
method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
{
  result := [];
  var current_max := numbers[0];
  result := result + [current_max];
  
  var i := 1;
  while i < |numbers|
    invariant 1 <= i <= |numbers|
    invariant |result| == i
    /* code modified by LLM (iteration 1): added invariant to ensure current_max is the maximum of numbers[0..i] */
    invariant current_max == result[i-1]
    invariant isMax(current_max, numbers[0..i])
    /* code modified by LLM (iteration 1): strengthened invariant to cover all valid indices */
    invariant forall j :: 0 < j < i ==> isMax(result[j], numbers[0..(j+1)])
  {
    /* code modified by LLM (iteration 1): added assertion to help verification */
    assert current_max in numbers[0..i];
    assert forall k :: 0 <= k < i ==> numbers[k] <= current_max;
    
    if numbers[i] > current_max {
      current_max := numbers[i];
    }
    
    /* code modified by LLM (iteration 1): added assertion to verify current_max is maximum of extended sequence */
    assert current_max >= numbers[i];
    assert current_max in numbers[0..(i+1)];
    assert forall k :: 0 <= k <= i ==> numbers[k] <= current_max;
    assert isMax(current_max, numbers[0..(i+1)]);
    
    result := result + [current_max];
    i := i + 1;
  }
}