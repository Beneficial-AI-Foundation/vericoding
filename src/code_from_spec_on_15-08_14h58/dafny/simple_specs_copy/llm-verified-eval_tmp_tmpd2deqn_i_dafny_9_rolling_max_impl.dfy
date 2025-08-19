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
        invariant forall i :: 0 < i < j ==> isMax(result[i], numbers[0..(i+1)])
    {
        var current_max := numbers[0];
        var k := 1;
        while k <= j
            invariant 1 <= k <= j + 1
            invariant current_max in numbers[0..(j+1)]
            invariant forall l :: 0 <= l < k ==> numbers[l] <= current_max
        {
            if numbers[k] > current_max {
                current_max := numbers[k];
            }
            k := k + 1;
        }
        
        result := result + [current_max];
        j := j + 1;
    }
}