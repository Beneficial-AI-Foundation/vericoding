function CalcBal(s: seq<int>, i: int, j: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1)
}
// pure-end
method correct_bracketing(s: seq<int>) returns (b: bool)
    // pre-conditions-start
    requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
    // pre-conditions-end
    // post-conditions-start
    ensures (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0) ==> b
    ensures b ==> (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0)
    // post-conditions-end
{
    // impl-start
    var i := 0;
    var depth := 0;
    b := true;
    while i < |s|
        // invariants-start
        invariant 0 <= i <= |s|
        invariant depth == CalcBal(s, 0, i)
        invariant (forall j :: 0 <= j <= i ==> CalcBal(s, 0, j) >= 0) ==> b
        invariant b ==> (forall j :: 0 <= j <= i ==> CalcBal(s, 0, j) >= 0)
        // invariants-end
    {
        if s[i] == 0 {
            depth := depth + 1;
        } else {
            depth := depth - 1;
        }
        if depth < 0 {
            b := false;
        }
        i := i + 1;
    }
    // impl-end
}
