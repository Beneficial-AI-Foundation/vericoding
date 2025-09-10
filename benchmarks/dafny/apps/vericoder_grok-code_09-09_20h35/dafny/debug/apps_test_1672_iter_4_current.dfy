predicate ValidInput(magnets: seq<string>)
{
    forall i :: 0 <= i < |magnets| ==> magnets[i] in {"01", "10"}
}

function CountGroups(magnets: seq<string>) : int
    requires ValidInput(magnets)
{
    if |magnets| == 0 then 0
    else 1 + |set i | 1 <= i < |magnets| && magnets[i] != magnets[i-1]|
}

// <vc-helpers>
function ChangeCount(magnets: seq<string>, k: nat): nat
    requires ValidInput(magnets) && k <= |magnets|
    ensures k >= 2 ==> ChangeCount(magnets, k) == ChangeCount(magnets, k-1) + (if magnets[k-1] != magnets[k-2] then 1 else 0)
{
    if k == 0 then 0
    else if k == 1 then 0
    else ChangeCount(magnets, k-1) + (if magnets[k-1] != magnets[k-2] then 1 else 0)
}

lemma SetEqChangeCount(magnets: seq<string>, n: nat)
requires ValidInput(magnets) && n <= |magnets|
decreases n
ensures ChangeCount(magnets, n) == |set i | 1 <= i < n && magnets[i] != magnets[i-1]|
{
if n <=1 {}
else {
SetEqChangeCount(magnets, n-1);
assert ChangeCount(magnets, n) == ChangeCount(magnets, n-1) + (if magnets[n-1] != magnets[n-2] then 1 else 0);
}
}
// </vc-helpers>

// <vc-spec>
method solve(magnets: seq<string>) returns (result: int)
    requires ValidInput(magnets)
    ensures result >= 0
    ensures |magnets| == 0 ==> result == 0
    ensures |magnets| > 0 ==> result >= 1
    ensures result <= |magnets|
    ensures result == CountGroups(magnets)
// </vc-spec>
// <vc-code>
{
    if |magnets| == 0 {
        result := 0;
    } else {
        result := 1;
        var i := 1;
        while i < |magnets|
            invariant 1 <= i <= |magnets|
            invariant result == 1 + ChangeCount(magnets, i)
            invariant 1 <= result <= i
        {
            if magnets[i] != magnets[i-1] {
                result := result + 1;
            }
            i := i + 1;
        }
        SetEqChangeCount(magnets, |magnets|);
        assert result == 1 + ChangeCount(magnets, |magnets|);
        assert CountGroups(magnets) == 1 + ChangeCount(magnets, |magnets|);
    }
}
// </vc-code>

