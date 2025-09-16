// <vc-preamble>
// ======= TASK =======
// Find and return the maximum element in a given list of numbers.
// The list must be non-empty. The maximum element is the largest value
// present in the list, and it must be an actual element of the list.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(l: seq<int>)
{
    |l| > 0
}

predicate IsMaxElement(l: seq<int>, max_val: int)
{
    max_val in l && forall i :: 0 <= i < |l| ==> l[i] <= max_val
}
// </vc-preamble>

// <vc-helpers>
function max_element_func(l: seq<int>): int
    requires |l| > 0
    ensures max_element_func(l) in l
    ensures forall i :: 0 <= i < |l| ==> l[i] <= max_element_func(l)
{
    if |l| == 1 then l[0]
    else
        var rest_max := max_element_func(l[1..]);
        if l[0] > rest_max then l[0] else rest_max
}
// </vc-helpers>

// <vc-spec>
method FindMaxElement(l: seq<int>) returns (max_val: int)
    requires ValidInput(l)
    ensures IsMaxElement(l, max_val)
// </vc-spec>
// <vc-code>
{
    max_val := max_element_func(l);
}
// </vc-code>
