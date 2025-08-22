// ATOM 
function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{
    if |s| == 0 || n == 0 then
        0
    else
        s[0] + sum(s[1..], n-1)
}


// ATOM 

lemma sum_plus(s: seq<int>, i: nat)
    requires i < |s|
    ensures sum(s, i) + s[i] == sum(s, i+1)
{
}


// IMPL below_zero

method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
    result := false;
    var i := 0;
    
    /* code modified by LLM (iteration 4): Fixed loop bound and invariants to properly verify all positions */
    while i <= |ops|
        invariant 0 <= i <= |ops| + 1
        invariant result ==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
        invariant !result ==> forall n: nat :: n < i && n <= |ops| ==> sum(ops, n) >= 0
    {
        /* code modified by LLM (iteration 4): Check if current sum is negative */
        if sum(ops, i) < 0 {
            result := true;
            return;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Assert that we've checked all valid positions */
    assert forall n: nat :: n <= |ops| ==> sum(ops, n) >= 0;
}