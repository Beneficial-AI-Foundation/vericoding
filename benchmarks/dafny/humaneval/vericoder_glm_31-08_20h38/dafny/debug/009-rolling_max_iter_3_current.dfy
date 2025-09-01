datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
// (no changes needed in helpers section)
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
    if |numbers| == 0 {
        return [];
    }
    var arr := new int[|numbers|];
    arr[0] := numbers[0];
    for i := 1 to |numbers|
        invariant 0 <= i <= |numbers|
        invariant arr.Length == |numbers|
        invariant forall j : int :: 0 <= j < i ==> numbers[j] <= arr[j]
        invariant forall j : int :: 0 <= j < i-1 ==> arr[j] <= arr[j+1]
    {
        arr[i] := if numbers[i] > arr[i-1] then numbers[i] else arr[i-1];
    }
    return arr[..];
}
// </vc-code>

