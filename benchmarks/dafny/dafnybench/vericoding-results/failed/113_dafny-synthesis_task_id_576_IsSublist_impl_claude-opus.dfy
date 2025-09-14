

// <vc-helpers>
lemma SublistFound(sub: seq<int>, main: seq<int>, i: int)
    requires 0 <= i <= |main| - |sub|
    requires sub == main[i..i + |sub|]
    ensures exists j :: 0 <= j <= |main| - |sub| && sub == main[j..j + |sub|]
{
    // Witness: j := i
    assert sub == main[i..i + |sub|];
}

lemma NoSublistExists(sub: seq<int>, main: seq<int>, k: int)
    requires 0 <= k <= |main| - |sub| + 1
    requires |sub| <= |main|
    requires forall j :: 0 <= j < k ==> sub != main[j..j + |sub|]
    ensures k == |main| - |sub| + 1 ==> !(exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
{
    if k == |main| - |sub| + 1 {
        forall i | 0 <= i <= |main| - |sub|
            ensures sub != main[i..i + |sub|]
        {
            assert 0 <= i < k;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// </vc-spec>
// <vc-code>
{
    if |sub| > |main| {
        return false;
    }
    
    var i := 0;
    while i <= |main| - |sub|
        invariant 0 <= i <= |main| - |sub| + 1
        invariant forall j :: 0 <= j < i ==> sub != main[j..j + |sub|]
    {
        if sub == main[i..i + |sub|] {
            SublistFound(sub, main, i);
            return true;
        }
        i := i + 1;
    }
    
    assert i == |main| - |sub| + 1;
    NoSublistExists(sub, main, i);
    return false;
}
// </vc-code>

