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
lemma sum_property(s: seq<int>, n: nat, m: nat)
    requires n <= |s| && m <= n
    ensures sum(s, m) + sum(s[m..], n - m) == sum(s, n)
{
    if m == 0 {
        assert s[0..] == s;
    } else if |s| == 0 || m == 0 {
    } else {
        sum_property(s[1..], n-1, m-1);
    }
}

lemma sum_incremental(s: seq<int>, n: nat)
    requires n < |s|
    ensures sum(s, n+1) == sum(s, n) + s[n]
{
    if n == 0 {
        if |s| > 0 {
            assert sum(s, 1) == s[0];
            assert sum(s, 0) == 0;
        }
    } else {
        sum_incremental(s[1..], n-1);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BelowZero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    result := false;
    var balance := 0;
    var i := 0;
    
    while i < |ops|
        invariant 0 <= i <= |ops|
        invariant balance == sum(ops, i)
        invariant !result ==> forall k: nat :: k <= i ==> sum(ops, k) >= 0
        invariant result ==> exists k: nat :: k <= i && sum(ops, k) < 0
    {
        balance := balance + ops[i];
        i := i + 1;
        
        sum_incremental(ops, i-1);
        
        if balance < 0 {
            result := true;
        }
    }
}
// </vc-code>
