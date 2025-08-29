datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma MonotonicityPreservation(numbers: seq<int>, result: seq<int>, i: int)
    requires |numbers| == |result|
    requires forall k : int :: k >= 0 && k < |numbers| ==> numbers[k] <= result[k]
    requires forall k : int :: k >= 0 && k + 1 < |numbers| ==> result[k] <= result[k + 1]
    ensures i >= 0 && i < |numbers| ==> numbers[i] <= result[i]
    ensures i >= 0 && i + 1 < |numbers| ==> result[i] <= result[i + 1]
{
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
method RollingMax(numbers: seq<int>) returns (result: seq<int>)
    ensures |numbers| == |result|
    ensures forall i : int :: i >= 0 && i < |numbers| ==> numbers[i] <= result[i]
    ensures forall i : int :: i >= 0 && i + 1 < |numbers| ==> result[i] <= result[i + 1]
{
    if |numbers| == 0 {
        result := [];
        return;
    }

    var res := new int[|numbers|];
    res[0] := numbers[0];
    var i := 1;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant forall k : int :: k >= 0 && k < i ==> res[k] >= numbers[k]
        invariant forall k : int :: k >= 0 && k + 1 < i ==> res[k] <= res[k + 1]
    {
        res[i] := if numbers[i] > res[i-1] then numbers[i] else res[i-1];
        i := i + 1;
    }
    result := res[..];
}
// </vc-code>
