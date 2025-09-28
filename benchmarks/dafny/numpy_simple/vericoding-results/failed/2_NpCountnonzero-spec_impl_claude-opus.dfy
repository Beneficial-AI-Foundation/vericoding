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
lemma NonzeroHelperSubarray(arr: seq<real>, i: nat)
    requires i <= |arr|
    ensures nonzero_helper(arr[i..]) == 
        if i == |arr| then 0
        else if arr[i] == 0.0 then nonzero_helper(arr[i+1..])
        else 1 + nonzero_helper(arr[i+1..])
{
    if i == |arr| {
        assert arr[i..] == [];
    } else {
        assert arr[i..][0] == arr[i];
        assert arr[i..][1..] == arr[i+1..];
    }
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
    result := 0;
    var i := 0;
    
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant result == nonzero_helper(arr[..i])
    {
        NonzeroHelperSubarray(arr[..], i);
        assert arr[..][i] == arr[i];
        assert arr[..][i+1..] == arr[i+1..];
        
        if arr[i] != 0.0 {
            result := result + 1;
        }
        i := i + 1;
        
        assert arr[..i] == arr[..i-1] + [arr[i-1]];
    }
    
    assert i == arr.Length;
    assert arr[..i] == arr[..];
}
// </vc-code>
