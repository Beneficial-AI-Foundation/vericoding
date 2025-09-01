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
    if |result| > 0 {
        var k := 0;
        while k < |result|
            invariant 0 <= k <= |result|
            invariant forall i, j :: 0 <= i <= j < k ==> result[i] <= result[j]
        {
            if k > 0 {
                assert result[k-1] <= result[k];
            }
            k := k + 1;
        }
    }
}

lemma max_property(a: int, b: int)
    ensures max(a, b) >= a && max(a, b) >= b
{
}

lemma sequence_property(result: seq<int>, current_max: int, i: int)
    requires |result| == i
    requires i > 0 ==> current_max == result[i-1]
    requires forall j :: 0 <= j < i ==> result[j] <= current_max
    ensures forall j, k :: 0 <= j <= k < i ==> result[j] <= result[k]
{
    if i > 0 {
        var j_var := 0;
        while j_var < i
            invariant 0 <= j_var <= i
            invariant forall x, y :: 0 <= x <= y < j_var ==> result[x] <= result[y]
        {
            var k_var := j_var;
            while k_var < i
                invariant j_var <= k_var <= i
                invariant forall x, y :: 0 <= x <= y < k_var ==> result[x] <= result[y]
            {
                if j_var < k_var {
                    assert result[j_var] <= current_max;
                    assert result[k_var] <= current_max;
                    if k_var == i-1 {
                        assert result[k_var] == current_max;
                    }
                }
                k_var := k_var + 1;
            }
            j_var := j_var + 1;
        }
    }
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
    result := [current_max];
    i := 1;
    
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
        max_property(current_max, numbers[i]);
        result := result + [current_max];
        sequence_property(result, current_max, i+1);
        i := i + 1;
    }
    
    monotonicity_property(result);
}
// </vc-code>

