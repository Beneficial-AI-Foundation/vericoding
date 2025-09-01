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
{
    result := [];
    if |numbers| == 0 {
        return;
    }
    
    var current_max := numbers[0];
    result := [current_max];
    
    var i := 1;
    while i < |numbers|
        invariant 1 <= i <= |numbers|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> numbers[j] <= result[j]
        invariant forall j :: 0 <= j < i - 1 ==> result[j] <= result[j + 1]
        invariant current_max == result[i - 1]
        invariant forall j :: 0 <= j < i ==> numbers[j] <= current_max
    {
        if numbers[i] > current_max {
            current_max := numbers[i];
        }
        result := result + [current_max];
        i := i + 1;
    }
}
// </vc-code>

