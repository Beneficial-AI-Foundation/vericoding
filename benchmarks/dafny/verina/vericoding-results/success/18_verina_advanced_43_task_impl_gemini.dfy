// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int {
    if a > b then a else b
}

function min(a: int, b: int): int {
    if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method MaxStrength(nums: array<int>) returns (result: int)
    requires nums.Length > 0
    ensures
        /* The result represents the maximum product of any non-empty subset of nums.
           For simplicity, we ensure that the result is at least as large as one of the elements. */
        exists i :: 0 <= i < nums.Length && result >= nums[i]
// </vc-spec>
// <vc-code>
{
    var max_so_far := nums[0];
    var min_so_far := nums[0];
    var i := 1;

    while i < nums.Length
        invariant 1 <= i <= nums.Length
        invariant exists j :: 0 <= j < i && max_so_far >= nums[j]
    {
        var current_num := nums[i];
        var old_max := max_so_far;
        var old_min := min_so_far;

        max_so_far := max(old_max, max(current_num, max(current_num * old_max, current_num * old_min)));
        min_so_far := min(old_min, min(current_num, min(current_num * old_max, current_num * old_min)));

        i := i + 1;
    }

    result := max_so_far;
}
// </vc-code>
