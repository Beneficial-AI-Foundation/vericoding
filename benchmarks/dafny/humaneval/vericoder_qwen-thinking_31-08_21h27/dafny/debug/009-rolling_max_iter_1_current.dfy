datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>

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
if |numbers| == 0 {
    return [];
}
var currentMax := numbers[0];
var result := [currentMax];
for i := 1 to |numbers| - 1 {
    if numbers[i] > currentMax {
        currentMax := numbers[i];
    }
    result := result + [currentMax];
    invariant |result| == i + 1
    invariant forall k : int :: 0 <= k <= i ==> numbers[k] <= result[k]
    invariant forall k : int :: 0 <= k < i ==> result[k] <= result[k+1]
}
return result;
// </vc-code>

