// <vc-preamble>
function nonzero_helper(arr: seq<real>): nat 
    decreases |arr|
{
    if |arr| == 0 then
        0
    else
        var rest_count := nonzero_helper(arr[1..]);
        if arr[0] == 0.0 then
            rest_count
        else
            rest_count + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma to handle relationship between full array and tail when first element is zero */
lemma nonzero_helper_extend(arr: seq<real>, i: int)
    requires 0 <= i < |arr|
    ensures nonzero_helper(arr[..i+1]) == nonzero_helper(arr[..i]) + (if arr[i] == 0.0 then 0 else 1)
{
    if i == 0 {
        assert arr[..0] == [];
        assert arr[..1] == [arr[0]];
        assert nonzero_helper([]) == 0;
        if arr[0] == 0.0 {
            assert nonzero_helper([arr[0]]) == 0;
        } else {
            assert nonzero_helper([arr[0]]) == 1;
        }
    } else {
        var prefix := arr[..i];
        var extended := arr[..i+1];
        assert extended == arr[..i] + [arr[i]];
        nonzero_helper_extend(arr, i-1);
    }
}

lemma nonzero_helper_properties(arr: seq<real>)
    ensures nonzero_helper(arr) <= |arr|
    ensures |arr| > 0 && arr[0] == 0.0 ==> nonzero_helper(arr) == nonzero_helper(arr[1..])
    ensures |arr| > 0 && arr[0] != 0.0 ==> nonzero_helper(arr) == nonzero_helper(arr[1..]) + 1
{
    if |arr| == 0 {
        // base case
    } else {
        nonzero_helper_properties(arr[1..]);
    }
}

lemma tail_relationship(arr: seq<real>)
    requires |arr| > 0 && arr[0] == 0.0
    ensures nonzero_helper(arr[1..]) == nonzero_helper(arr)
{
    nonzero_helper_properties(arr);
}
// </vc-helpers>

// <vc-spec>
method nonzero(arr: array<real>) returns (result: int)
    ensures 
        result <= arr.Length &&
        result == nonzero_helper(arr[..]) &&
        (arr.Length > 0 && arr[0] == 0.0 ==> 
            nonzero_helper(arr[1..]) == if result > 0 then result - 1 else 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Properly establish tail relationship for postcondition */
    result := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant result == nonzero_helper(arr[..i])
        invariant result <= i
    {
        nonzero_helper_extend(arr[..], i);
        if arr[i] != 0.0 {
            result := result + 1;
        }
        i := i + 1;
    }
    assert arr[..] == arr[..arr.Length];
    nonzero_helper_properties(arr[..]);
    
    if arr.Length > 0 && arr[0] == 0.0 {
        tail_relationship(arr[..]);
        assert nonzero_helper(arr[1..]) == nonzero_helper(arr[..]);
        assert result == nonzero_helper(arr[..]);
        assert nonzero_helper(arr[1..]) == result;
        if result > 0 {
            assert false; // This case is impossible when arr[0] == 0.0
        } else {
            assert nonzero_helper(arr[1..]) == 0;
        }
    }
}
// </vc-code>
