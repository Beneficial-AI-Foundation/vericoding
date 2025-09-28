// <vc-preamble>

predicate IsPositive(x: int)
{
    x > 0
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> IsPositive(s[i])
}

predicate AllElementsFromOriginal(result: seq<int>, original: seq<int>)
{
    forall x :: x in result ==> x in original
}

predicate ContainsAllPositives(result: seq<int>, original: seq<int>)
{
    forall i :: 0 <= i < |original| && IsPositive(original[i]) ==> original[i] in result
}

predicate PreservesOrder(result: seq<int>, original: seq<int>)
{
    forall i, j :: 0 <= i < j < |result| ==> 
        (exists k1, k2 :: (0 <= k1 < k2 < |original| && original[k1] == result[i] && original[k2] == result[j] &&
        forall k :: k1 < k < k2 ==> !IsPositive(original[k])))
}

function CountPositives(s: seq<int>): int
{
    |set x | x in s && IsPositive(x)|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed parse errors related to tuple return type and while loop syntax. */
function FindNextPositive(s: seq<int>, start_index: int): (index: int, value: int)
    requires 0 <= start_index <= |s|
    ensures (start_index <= index < |s| && IsPositive(s[index])) || (index == |s|)
    ensures (start_index <= index < |s| && value == s[index]) || (index == |s| && value == -1)
{
    var i := start_index;
    while i < |s|
        invariant start_index <= i <= |s|;
    {
        if IsPositive(s[i]) {
            return (i, s[i]);
        }
        i := i + 1;
    }
    return (|s|, -1);
}
// </vc-helpers>

// <vc-spec>
method get_positive(l: seq<int>) returns (result: seq<int>)
    ensures AllPositive(result)
    ensures AllElementsFromOriginal(result, l)
    ensures ContainsAllPositives(result, l)
    ensures |result| == CountPositives(l)
    ensures PreservesOrder(result, l)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors and refined invariants to aid verification of `PreservesOrder` and `ContainsAllPositives`. */
{
    var result_seq: seq<int> := [];
    var current_index := 0;

    while current_index < |l|
        invariant 0 <= current_index <= |l|
        invariant AllPositive(result_seq)
        invariant AllElementsFromOriginal(result_seq, l)
        invariant forall i :: 0 <= i < current_index && IsPositive(l[i]) ==> l[i] in result_seq // All positives up to current_index are in result_seq
        invariant |result_seq| <= CountPositives(l[0 .. current_index]) // Number of positives in result_seq is a subset of positives in processed `l`
        invariant PreservesOrder(result_seq, l[0 .. current_index]) // Preserves order for elements added from l[0 .. current_index]

    {
        var next_pos_index: int;
        var next_pos_value: int;
        (next_pos_index, next_pos_value) := FindNextPositive(l, current_index);

        if next_pos_index < |l| {
            result_seq := result_seq + [next_pos_value];
            current_index := next_pos_index + 1;
        } else {
            current_index := |l|; // No more positive numbers found
        }
    }
    return result_seq;
}
// </vc-code>
