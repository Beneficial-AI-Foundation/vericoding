datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
function max(a: int, b: int): int {
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
    var n := |numbers|;
    if n == 0 {
        return [];
    }

    var result_arr := new int[n];
    result_arr[0] := numbers[0];

    var i := 1;
    while i < n
        invariant 0 <= i <= n
        invariant result_arr.Length == n
        invariant result_arr[0] == numbers[0]
        invariant forall k :: 0 <= k < i ==> numbers[k] <= result_arr[k]
        invariant forall k :: 0 <= k + 1 < i ==> result_arr[k] <= result_arr[k+1]
        invariant forall k :: 0 <= k < i ==> result_arr[k] == (if k == 0 then numbers[0] else max(numbers[k], result_arr[k-1]))
    {
        result_arr[i] := max(numbers[i], result_arr[i-1]);
        i := i + 1;
    }

    result := result_arr[..];
    return result;
}
// </vc-code>

