// <vc-preamble>
// ======= TASK =======
// Given a list of integers, return a list where each element represents 
// the maximum value encountered from the beginning of the list up to and 
// including the current position.

// ======= SPEC REQUIREMENTS =======
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
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
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
    if |numbers| == 0 {
        return [];
    }

    result := [];
    var current_max := numbers[0];

    for i := 0 to |numbers|
        invariant |result| == i
        invariant i > 0 ==> current_max == max_up_to(numbers, i - 1)
        invariant forall k :: 0 <= k < i ==> result[k] == max_up_to(numbers, k)
        invariant forall k :: 0 <= k < i ==> 
            forall j :: 0 <= j <= k ==> numbers[j] <= result[k]
        invariant forall k :: 0 <= k < i ==> 
            exists j :: 0 <= j <= k && numbers[j] == result[k]
    {
        current_max := if current_max > numbers[i] then current_max else numbers[i];
        result := result + [current_max];
    }
}
// </vc-code>
