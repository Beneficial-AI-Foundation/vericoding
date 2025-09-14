predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(s: string, result: string)
{
    |result| == |s| && forall i :: 0 <= i < |result| ==> result[i] == 'x'
}

// <vc-helpers>
lemma ValidOutputProperty(s: string, result: string, k: nat)
    requires k <= |s|
    requires |result| == k
    requires forall i :: 0 <= i < k ==> result[i] == 'x'
    ensures |result + ['x']| == k + 1
    ensures forall i :: 0 <= i < k + 1 ==> (result + ['x'])[i] == 'x'
{
    assert |result + ['x']| == |result| + |['x']| == k + 1;
    forall i | 0 <= i < k + 1
        ensures (result + ['x'])[i] == 'x'
    {
        if i < k {
            assert (result + ['x'])[i] == result[i] == 'x';
        } else {
            assert i == k;
            assert (result + ['x'])[i] == ['x'][0] == 'x';
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
    result := "";
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == 'x'
    {
        ValidOutputProperty(s, result, i);
        result := result + ['x'];
        i := i + 1;
    }
}
// </vc-code>

