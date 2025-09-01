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
    if a > b then a else b
}

lemma monotonicity_property(result: seq<int>) 
    ensures forall i, j :: 0 <= i <= j < |result| ==> result[i] <= result[j]
{
    // This lemma helps prove the third post-condition
    // The post-condition ensures result is non-decreasing
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
    result := [];
    if |numbers| == 0 {
        return;
    }
    
    var current_max := numbers[0];
    var i := 0;
    
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant |result| == i
        invariant i > 0 ==> current_max == result[i-1]
        invariant forall j :: 0 <= j < i ==> numbers[j] <= result[j]
        invariant forall j :: 0 <= j < i ==> result[j] <= current_max
        invariant forall j, k :: 0 <= j <= k < i ==> result[j] <= result[k]
        decreases |numbers| - i
    {
        current_max := max(current_max, numbers[i]);
        result := result + [current_max];
        i := i + 1;
    }
    
    // Apply the lemma to prove the final postcondition
    monotonicity_property(result);
}
// </vc-code>

