// ATOM 
function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}


//IMPL max
method max(numbers: seq<int>) returns (result: int)
requires numbers != []
ensures isMax(result, numbers)
{
    result := numbers[0];
    var i := 1;
    while i < |numbers|
        invariant 1 <= i <= |numbers|
        invariant result in numbers[0..i]
        invariant forall j :: 0 <= j < i ==> numbers[j] <= result
    {
        if numbers[i] > result {
            result := numbers[i];
        }
        i := i + 1;
    }
}


//IMPL rolling_max
method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
{
    result := [];
    var i := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant |result| == i
        invariant forall j :: 0 < j < i ==> isMax(result[j], numbers[0..(j+1)])
    {
        if i == 0 {
            result := result + [numbers[0]];
        } else {
            var current_max := max(numbers[0..(i+1)]);
            result := result + [current_max];
        }
        i := i + 1;
    }
}