/* 
HumanEvalX 3
You're given a list of deposit and withdrawal operations on a bank account that starts with zero balance. 
Your task is to detect if at any point the balance of account falls below zero, and at that point function 
should return True. Otherwise it should return False.
*/

function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{
    if |s| == 0 || n == 0 then
        0
    else
        s[0] + sum(s[1..], n-1)
}

// <vc-helpers>
lemma SumLemma(s: seq<int>, n: nat)
    requires n < |s|
    ensures sum(s, n+1) == sum(s, n) + s[n]
{
    if n == 0 {
        assert sum(s, 1) == s[0] + sum(s[1..], 0) == s[0] + 0 == s[0];
        assert sum(s, 0) == 0;
    } else {
        assert sum(s, n+1) == s[0] + sum(s[1..], n);
        SumLemma(s[1..], n-1);
        assert sum(s[1..], n) == sum(s[1..], n-1) + s[1..][n-1];
        assert s[1..][n-1] == s[n];
        assert sum(s, n) == s[0] + sum(s[1..], n-1);
        assert sum(s, n+1) == s[0] + sum(s[1..], n-1) + s[n] == sum(s, n) + s[n];
    }
}
// </vc-helpers>

// <vc-spec>
method BelowZero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    var balance := 0;
    var i := 0;
    
    while i < |ops|
        invariant 0 <= i <= |ops|
        invariant balance == sum(ops, i)
        invariant forall k: nat :: k <= i ==> sum(ops, k) >= 0
    {
        SumLemma(ops, i);
        balance := balance + ops[i];
        i := i + 1;
        
        if balance < 0 {
            assert sum(ops, i) == balance < 0;
            return true;
        }
    }
    
    assert i == |ops|;
    assert forall k: nat :: k <= |ops| ==> sum(ops, k) >= 0;
    return false;
}
// </vc-code>

