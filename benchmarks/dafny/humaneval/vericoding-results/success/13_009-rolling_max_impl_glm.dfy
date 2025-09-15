// <vc-preamble>
datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result : seq<int>)

    ensures |numbers| == |result|
    ensures forall i : int :: i >= 0 && i < |numbers| ==> numbers[i] <= result[i]
    ensures forall i : int :: i >= 0 && i + 1 < |numbers| ==> result[i] <= result[i + 1]
// </vc-spec>
// <vc-code>
{
    if |numbers| == 0 {
        return [];
    }
    var currentMax := numbers[0];
    result := [currentMax];
    var i := 1;
    while i < |numbers|
        invariant 0 < i <= |numbers|
        invariant |result| == i
        invariant forall j : int :: j >= 0 && j < i ==> numbers[j] <= result[j]
        invariant forall j : int :: j >= 0 && j + 1 < i ==> result[j] <= result[j + 1]
        invariant currentMax == result[i-1]
    {
        currentMax := max(currentMax, numbers[i]);
        result := result + [currentMax];
        i := i + 1;
    }
}
// </vc-code>
