datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
function max(a: int, b: int): int
{
    if a >= b then a else b
}

function rollingMaxAux(numbers: seq<int>, i: int): seq<int>
    requires 0 <= i <= |numbers|
    ensures |rollingMaxAux(numbers, i)| == i
    decreases i
{
    if i == 0 then []
    else if i == 1 then [numbers[0]]
    else rollingMaxAux(numbers, i-1) + [max(numbers[i-1], rollingMaxAux(numbers, i-1)[i-2])]
}

lemma rollingMaxAuxProperties(numbers: seq<int>, i: int)
    requires 0 < i <= |numbers|
    ensures |rollingMaxAux(numbers, i)| == i
    ensures i > 0 ==> rollingMaxAux(numbers, i)[0] == numbers[0]
{
    if i == 1 {
        assert rollingMaxAux(numbers, 1) == [numbers[0]];
    } else {
        rollingMaxAuxProperties(numbers, i-1);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def rolling_max(numbers: List[int]) -> Tuple[int, int]
From a given list of integers, generate a list of rolling maximum element found until given moment in the sequence.
*/
// </vc-description>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result: seq<int>)
    requires |numbers| > 0
    ensures |result| == |numbers|
    ensures forall i :: 0 <= i < |result| ==> result[i] == rollingMaxAux(numbers, i+1)[i]
    ensures |result| > 0 ==> result[0] == numbers[0]
// </vc-spec>
// <vc-code>
{
    result := [];
    if |numbers| == 0 {
        return;
    }
    
    var currentMax := numbers[0];
    result := result + [currentMax];
    
    var i := 1;
    while i < |numbers|
        invariant 1 <= i <= |numbers|
        invariant |result| == i
        invariant result[0] == numbers[0]
        invariant currentMax == rollingMaxAux(numbers, i)[i-1]
        invariant forall j :: 0 <= j < i ==> result[j] == rollingMaxAux(numbers, j+1)[j]
    {
        currentMax := max(currentMax, numbers[i]);
        result := result + [currentMax];
        rollingMaxAuxProperties(numbers, i+1);
        i := i + 1;
    }
}
// </vc-code>
