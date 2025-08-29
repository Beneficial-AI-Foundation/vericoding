datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires exists i : int :: mx == Some(i)
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma rolling_max_invariant(numbers: seq<int>, result: seq<int>, i: int)
    requires 0 <= i <= |numbers|
    requires |result| == i
    requires forall j :: 0 <= j < i ==> numbers[j] <= result[j]
    requires forall j :: 0 <= j < i - 1 ==> result[j] <= result[j + 1]
    ensures i > 0 ==> (forall j :: 0 <= j < i ==> numbers[j] <= result[i-1])
{
    if i > 0 {
        forall j | 0 <= j < i
            ensures numbers[j] <= result[i-1]
        {
            if j < i - 1 {
                assert numbers[j] <= result[j];
                monotonic_sequence_helper(result, j, i-1);
                assert result[j] <= result[i-1];
                assert numbers[j] <= result[i-1];
            } else {
                assert j == i - 1;
                assert numbers[j] <= result[j];
                assert j == i - 1;
                assert numbers[j] <= result[i-1];
            }
        }
    }
}

lemma monotonic_sequence_helper(result: seq<int>, start: int, end: int)
    requires 0 <= start <= end < |result|
    requires forall j :: 0 <= j < |result| - 1 ==> result[j] <= result[j + 1]
    ensures result[start] <= result[end]
    decreases end - start
{
    if start < end {
        monotonic_sequence_helper(result, start + 1, end);
        assert result[start] <= result[start + 1];
        assert result[start + 1] <= result[end];
    }
}

lemma monotonic_helper(result: seq<int>, i: int, max_so_far: int)
    requires 0 < i
    requires |result| == i
    requires forall j :: 0 <= j < i - 1 ==> result[j] <= result[j + 1]
    requires max_so_far >= result[i-1]
    ensures forall j :: 0 <= j < i ==> result[j] <= max_so_far
{
    forall j | 0 <= j < i
        ensures result[j] <= max_so_far
    {
        if j < i - 1 {
            monotonic_sequence_helper(result, j, i-1);
            assert result[j] <= result[i-1];
            assert result[i-1] <= max_so_far;
        } else {
            assert j == i - 1;
            assert result[j] <= max_so_far;
        }
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
    var i := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> numbers[j] <= result[j]
        invariant forall j :: 0 <= j < i - 1 ==> result[j] <= result[j + 1]
    {
        var max_so_far := numbers[i];
        if i > 0 {
            rolling_max_invariant(numbers, result, i);
            assert forall j :: 0 <= j < i ==> numbers[j] <= result[i-1];
            if result[i-1] > max_so_far {
                max_so_far := result[i-1];
            }
            monotonic_helper(result, i, max_so_far);
            assert forall j :: 0 <= j < i ==> result[j] <= max_so_far;
        }
        result := result + [max_so_far];
        i := i + 1;
    }
}
// </vc-code>

