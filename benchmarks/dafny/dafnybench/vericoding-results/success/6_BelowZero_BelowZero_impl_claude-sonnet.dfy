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
lemma SumProperty(s: seq<int>, n: nat)
    requires n <= |s|
    ensures sum(s, n) == if n == 0 then 0 else sum(s, n-1) + s[n-1]
{
    if n == 0 {
        assert sum(s, n) == 0;
    } else if |s| == 0 {
        assert sum(s, n) == 0;
    } else {
        calc {
            sum(s, n);
            s[0] + sum(s[1..], n-1);
            {
                if n == 1 {
                    assert sum(s[1..], n-1) == 0;
                    assert s[0] == s[n-1];
                } else {
                    SumProperty(s[1..], n-1);
                    assert sum(s[1..], n-1) == sum(s[1..], n-2) + s[1..][n-2];
                    assert s[1..][n-2] == s[n-1];
                }
            }
            sum(s, n-1) + s[n-1];
        }
    }
}

lemma SumIncremental(s: seq<int>, n: nat)
    requires n < |s|
    ensures sum(s, n+1) == sum(s, n) + s[n]
{
    SumProperty(s, n+1);
}

lemma SumNonNegativeBase(s: seq<int>)
    ensures sum(s, 0) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method BelowZero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    result := false;
    var balance := 0;
    var i := 0;
    
    SumNonNegativeBase(ops);
    
    while i < |ops|
        invariant 0 <= i <= |ops|
        invariant balance == sum(ops, i)
        invariant !result ==> forall k: nat :: k <= i ==> sum(ops, k) >= 0
        invariant result ==> exists k: nat :: k <= i && sum(ops, k) < 0
    {
        balance := balance + ops[i];
        i := i + 1;
        
        SumIncremental(ops, i-1);
        assert balance == sum(ops, i);
        
        if balance < 0 {
            result := true;
            assert sum(ops, i) < 0;
            return;
        }
    }
    
    assert i == |ops|;
    assert balance == sum(ops, |ops|);
    assert forall k: nat :: k <= |ops| ==> sum(ops, k) >= 0;
}
// </vc-code>

