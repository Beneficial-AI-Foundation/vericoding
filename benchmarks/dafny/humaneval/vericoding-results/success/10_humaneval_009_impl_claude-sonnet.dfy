// <vc-preamble>

function max_up_to(numbers: seq<int>, index: int): int
    requires 0 <= index < |numbers|
{
    if index == 0 then numbers[0]
    else 
        var prev_max := max_up_to(numbers, index - 1);
        if numbers[index] > prev_max then numbers[index] else prev_max
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma to prove max_up_to properties for verification */
lemma max_up_to_properties(numbers: seq<int>, i: int)
    requires 0 <= i < |numbers|
    ensures forall j :: 0 <= j <= i ==> numbers[j] <= max_up_to(numbers, i)
    ensures exists j :: 0 <= j <= i && numbers[j] == max_up_to(numbers, i)
{
    if i == 0 {
        // Base case: max_up_to(numbers, 0) == numbers[0]
        assert numbers[0] == max_up_to(numbers, 0);
        assert exists j :: 0 <= j <= 0 && numbers[j] == max_up_to(numbers, 0);
    } else {
        max_up_to_properties(numbers, i - 1);
        var prev_max := max_up_to(numbers, i - 1);
        if numbers[i] > prev_max {
            // max_up_to(numbers, i) == numbers[i]
            assert exists j :: 0 <= j <= i && numbers[j] == max_up_to(numbers, i);
        } else {
            // max_up_to(numbers, i) == prev_max
            assert exists j :: 0 <= j <= i-1 && numbers[j] == prev_max;
            assert exists j :: 0 <= j <= i && numbers[j] == max_up_to(numbers, i);
        }
    }
}

lemma max_up_to_recurrence(numbers: seq<int>, i: int)
    requires 0 < i < |numbers|
    ensures max_up_to(numbers, i) == if numbers[i] > max_up_to(numbers, i-1) then numbers[i] else max_up_to(numbers, i-1)
{
    // This follows directly from the definition
}
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result: seq<int>)
    ensures |result| == |numbers|
    ensures |numbers| == 0 ==> |result| == 0
    ensures |numbers| > 0 ==> |result| > 0
    ensures forall i :: 0 <= i < |result| ==> 
        result[i] == max_up_to(numbers, i)
    ensures forall i :: 0 <= i < |result| ==> 
        forall j :: 0 <= j <= i ==> numbers[j] <= result[i]
    ensures forall i :: 0 <= i < |result| ==> 
        exists j :: 0 <= j <= i && numbers[j] == result[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added explicit assertions for base case */
    if |numbers| == 0 {
        result := [];
        return;
    }
    
    result := [numbers[0]];
    max_up_to_properties(numbers, 0);
    
    var i := 1;
    while i < |numbers|
        invariant 1 <= i <= |numbers|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == max_up_to(numbers, k)
        invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j <= k ==> numbers[j] <= result[k]
        invariant forall k :: 0 <= k < i ==> exists j :: 0 <= j <= k && numbers[j] == result[k]
    {
        max_up_to_properties(numbers, i);
        if i > 0 {
            max_up_to_recurrence(numbers, i);
        }
        var current_max := if numbers[i] > result[i-1] then numbers[i] else result[i-1];
        result := result + [current_max];
        i := i + 1;
    }
}
// </vc-code>
