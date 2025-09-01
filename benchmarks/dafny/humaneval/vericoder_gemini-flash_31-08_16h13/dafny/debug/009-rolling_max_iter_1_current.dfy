datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
function max_of_two(a: int, b: int): int
    ensures max_of_two(a, b) == a || max_of_two(a, b) == b
    ensures max_of_two(a, b) >= a
    ensures max_of_two(a, b) >= b
{
    if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result : seq<int>)
    // post-conditions-start
    ensures |numbers| == |result|
    ensures forall i : int :: i >= 0 && i < |numbers| ==> numbers[i] <= result[i]
    ensures forall i : int :: i >= 0 && i + 1 < |numbers| ==> result[i] <= result[i + 1]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    result := new int[|numbers|];
    if |numbers| == 0 {
        return;
    }

    result[0] := numbers[0];
    var i := 1;
    while i < |numbers|
        invariant 0 < i <= |numbers|
        invariant |result| == |numbers|
        invariant forall k :: 0 <= k < i ==> numbers[k] <= result[k]
        invariant forall k :: 0 <= k < i - 1 ==> result[k] <= result[k + 1]
        invariant result[i-1] == (if i-1 == 0 then numbers[0] else max_of_two(numbers[i-1], result[i-2]))
        decreases |numbers| - i
    {
        result[i] := max_of_two(numbers[i], result[i - 1]);
        i := i + 1;
    }
}
// </vc-code>

