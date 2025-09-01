function CalcBal(s: seq<int>, i: int, j: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1)
}

// <vc-helpers>
function IsBalanced(s: seq<int>, length: int) : bool
    requires 0 <= length <= |s|
    reads s
    //ensures IsBalanced(s, length) == (forall i :: 0 <= i <= length ==> CalcBal(s, 0, i) >= 0)
    decreases length
// This function determines if a sequence of integers represents a correctly bracketed expression.
// An expression is correctly bracketed if:
// 1. The balance (number of open brackets minus closed brackets) never drops below zero.
// 2. The final balance is zero.
{
    if length == 0 then
        true // An empty sequence is
    else if CalcBal(s, 0, length) < 0 then
        false // If the balance drops below zero at any point, it's not balanced.
    else
        // Recursively check the sub-sequence.
        // We know CalcBal(s, 0, length) >= 0.
        // What we need to ensure is that all intermediate CalcBal values are also non-negative.
        IsBalanced(s, length - 1)
}
// </vc-helpers>

// <vc-spec>
method correct_bracketing(s: seq<int>) returns (b: bool)
    // pre-conditions-start
    requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
    // pre-conditions-end
    // post-conditions-start
    ensures (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0) ==> b
    ensures b ==> (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    b := (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0) && (CalcBal(s, 0, |s|) == 0);
}
// </vc-code>

