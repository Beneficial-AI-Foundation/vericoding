// ATOM 
function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m
}

//ATOM_PLACEHOLDER_max

// IMPL 
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
        invariant forall j :: 0 < j < i ==> isMax(result[j], numbers[0..(j+1)])
        /* code modified by LLM (iteration 1): added invariant to track that current_max is the maximum of elements seen so far */
        invariant current_max in numbers[0..i]
        invariant forall k :: 0 <= k < i ==> numbers[k] <= current_max
    {
        /* code modified by LLM (iteration 1): updated condition to use >= instead of > to handle duplicates correctly */
        if numbers[i] >= current_max {
            current_max := numbers[i];
        }
        result := result + [current_max];
        i := i + 1;
    }
}