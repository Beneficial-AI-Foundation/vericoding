// <vc-preamble>
// ======= TASK =======
// Given a list of integers, transform each element based on its index:
// - If index is a multiple of 3: square the element
// - If index is a multiple of 4 but not a multiple of 3: cube the element  
// - Otherwise: keep the element unchanged
// Return the sum of all transformed elements.

// ======= SPEC REQUIREMENTS =======
function transform_element(value: int, index: int): int
{
    if index % 3 == 0 then value * value
    else if index % 4 == 0 then value * value * value
    else value
}

function sum_partial(lst: seq<int>, n: int): int
    requires 0 <= n <= |lst|
{
    if n == 0 then 0
    else sum_partial(lst, n-1) + transform_element(lst[n-1], n-1)
}

function sum_transformed(lst: seq<int>): int
{
    sum_partial(lst, |lst|)
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method sum_squares(lst: seq<int>) returns (result: int)
    ensures result == sum_transformed(lst)
// </vc-spec>
// <vc-code>
{
    if |lst| == 0 {
        result := 0;
        return;
    }

    result := 0;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant result == sum_partial(lst, i)
    {
        var value := lst[i];
        if i % 3 == 0 {
            result := result + value * value;
        } else if i % 4 == 0 {
            result := result + value * value * value;
        } else {
            result := result + value;
        }
        i := i + 1;
    }
}
// </vc-code>
