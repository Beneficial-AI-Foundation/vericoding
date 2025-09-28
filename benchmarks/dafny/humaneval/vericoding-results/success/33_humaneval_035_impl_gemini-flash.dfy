// <vc-preamble>

predicate ValidInput(l: seq<int>)
{
    |l| > 0
}

predicate IsMaxElement(l: seq<int>, max_val: int)
{
    max_val in l && forall i :: 0 <= i < |l| ==> l[i] <= max_val
}
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed termination error by adding a decreases clause and ensures clause issue by extending the range to cover 'in' operator to ensure the maximum value is within the given sub-sequence. */
function MaxElementHelper(l: seq<int>, start: int, end: int): int
 requires 0 <= start <= end < |l|
 ensures MaxElementHelper(l, start, end) in l[start..end+1]
 ensures forall i :: start <= i <= end ==> l[i] <= MaxElementHelper(l, start, end)
 decreases end - start
{
 if start == end then l[start]
 else
 var mid := (start + end) / 2;
 var max1 := MaxElementHelper(l, start, mid);
 var max2 := MaxElementHelper(l, mid + 1, end);
 if max1 > max2 then max1 else max2
}
// </vc-helpers>

// <vc-spec>
method FindMaxElement(l: seq<int>) returns (max_val: int)
    requires ValidInput(l)
    ensures IsMaxElement(l, max_val)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): The code for finding the max element iterates through the sequence and updates max_val as necessary, effectively implementing the IsMaxElement postcondition. */
{
    max_val := l[0];
    var i := 1;
    while i < |l|
        invariant 0 < i <= |l|
        invariant max_val in l[..i]
        invariant forall j :: 0 <= j < i ==> l[j] <= max_val
    {
        if l[i] > max_val {
            max_val := l[i];
        }
        i := i + 1;
    }
}
// </vc-code>
