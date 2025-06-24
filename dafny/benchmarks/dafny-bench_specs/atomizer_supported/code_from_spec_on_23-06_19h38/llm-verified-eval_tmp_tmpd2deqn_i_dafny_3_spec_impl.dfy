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
    var i := 0;
    var current_sum := 0;
    
    while i < |ops|
        invariant 0 <= i <= |ops|
        invariant current_sum == sum(ops, i)
        /* code modified by LLM (iteration 3): maintain that all prefix sums up to i are non-negative */
        invariant forall k: nat :: k <= i ==> sum(ops, k) >= 0
    {
        sum_plus(ops, i);
        /* code modified by LLM (iteration 3): compute next sum and check if it becomes negative */
        current_sum := current_sum + ops[i];
        i := i + 1;
        
        if current_sum < 0 {
            assert sum(ops, i) < 0;
            assert exists n: nat :: n <= |ops| && sum(ops, n) < 0;
            result := true;
            return;
        }
    }
    
    /* code modified by LLM (iteration 3): all prefix sums are non-negative */
    assert forall k: nat :: k <= |ops| ==> sum(ops, k) >= 0;
    result := false;
}