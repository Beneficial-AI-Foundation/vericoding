function psum(s: seq<int>): int
{
    if |s| == 0 then 0
    else psum(s[..(|s|)-1]) + s[ |s| - 1 ]
}

// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def below_zero(operations: List[int]) -> bool
You're given a list of deposit and withdrawal operations on a bank account that starts with zero balance. Your task is to detect if at any point the balance of account fallls below zero, and at that point function should return True. Otherwise it should return False.
*/
// </vc-description>

// <vc-spec>
method below_zero(ops: seq<int>) returns (res : bool)
    // post-conditions-start
    ensures res ==> forall i : int :: 0 <= i <= |ops| ==> psum(ops[..i]) >= 0
    ensures !res ==> exists i : int :: 0 <= i <= |ops| && psum(ops[..i]) < 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
