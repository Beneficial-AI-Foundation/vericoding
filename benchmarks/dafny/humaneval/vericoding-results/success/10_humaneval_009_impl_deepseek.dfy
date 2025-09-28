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
function max(a: int, b: int): int { if a > b then a else b }

/* helper modified by LLM (iteration 2): Added lemma to prove max_up_to properties */
lemma max_up_to_properties(numbers: seq<int>, index: int)
    requires 0 <= index < |numbers|
    ensures max_up_to(numbers, index) == max_up_to(numbers, index)
    ensures forall j :: 0 <= j <= index ==> numbers[j] <= max_up_to(numbers, index)
    ensures exists j :: 0 <= j <= index && numbers[j] == max_up_to(numbers, index)
{
    if index > 0 {
        max_up_to_properties(numbers, index - 1);
    }
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
    /* code modified by LLM (iteration 2): Fixed while loop invariants and added lemma calls */
    if |numbers| == 0 {
        result := [];
    } else {
        result := [numbers[0]];
        var i := 1;
        while i < |numbers|
            invariant 0 < i <= |numbers|
            invariant |result| == i
            invariant forall k :: 0 <= k < i ==> result[k] == max_up_to(numbers, k)
            invariant forall k :: 0 <= k < i ==> 
                (forall j :: 0 <= j <= k ==> numbers[j] <= result[k])
            invariant forall k :: 0 <= k < i ==> 
                (exists j :: 0 <= j <= k && numbers[j] == result[k])
        {
            max_up_to_properties(numbers, i-1);
            var current_max := max(result[i-1], numbers[i]);
            result := result + [current_max];
            i := i + 1;
        }
    }
}
// </vc-code>
