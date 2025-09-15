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
function max_up_to(numbers: seq<int>, i: int): int
    requires 0 <= i < |numbers|
{
    if i == 0 then numbers[0]
    else if numbers[i] > max_up_to(numbers, i - 1) then numbers[i]
    else max_up_to(numbers, i - 1)
}

lemma max_up_to_bound(numbers: seq<int>, i: int, j: int)
    requires 0 <= j <= i < |numbers|
    ensures numbers[j] <= max_up_to(numbers, i)
{
    if i == 0 {
    } else {
        if j == i {
        } else {
            max_up_to_bound(numbers, i - 1, j);
        }
    }
}

lemma max_up_to_monotonic(numbers: seq<int>, i: int)
    requires 0 <= i < |numbers| - 1
    ensures max_up_to(numbers, i) <= max_up_to(numbers, i + 1)
{
}
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result : seq<int>)

    ensures |numbers| == |result|
    ensures forall i : int :: i >= 0 && i < |numbers| ==> numbers[i] <= result[i]
    ensures forall i : int :: i >= 0 && i + 1 < |numbers| ==> result[i] <= result[i + 1]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed array/sequence type mismatch by using sequence construction */
    if |numbers| == 0 {
        result := [];
        return;
    }
    
    result := [max_up_to(numbers, 0)];
    
    var i := 1;
    while i < |numbers|
        invariant 1 <= i <= |numbers|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == max_up_to(numbers, j)
    {
        max_up_to_bound(numbers, i, i);
        if i > 0 {
            max_up_to_monotonic(numbers, i - 1);
        }
        
        var current_max := max_up_to(numbers, i);
        result := result + [current_max];
        
        i := i + 1;
    }
    
    forall j | 0 <= j < |numbers| {
        max_up_to_bound(numbers, j, j);
    }
    
    forall j | 0 <= j < |numbers| - 1 {
        max_up_to_monotonic(numbers, j);
    }
}
// </vc-code>
