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
    ensures IsBalanced(s, length) == (forall i :: 0 <= i <= length ==> CalcBal(s, 0, i) >= 0)
{
    if length == 0 then
        true
    else if CalcBal(s, 0, length) < 0 then
        false
    else
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
    b := IsBalanced(s, |s|);
}
// </vc-code>

