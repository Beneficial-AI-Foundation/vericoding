//ATOM

function total (a: seq<nat>) : nat
{
 if |a| == 0 then 0
 else total (a[0..|a|-1]) + a[|a|-1]
}

//IMPL 

method Total (a: seq<nat>) returns (r:nat)
 ensures r == total (a[0..|a|])
{
    r := 0;
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant r == total(a[0..i])
    {
        /* code modified by LLM (iteration 1): added lemma call to prove total(a[0..i+1]) == total(a[0..i]) + a[i] */
        totalIncrementalLemma(a, i);
        
        r := r + a[i];
        i := i + 1;
    }
}

/* code modified by LLM (iteration 1): added helper lemma to prove incremental property of total function */
lemma totalIncrementalLemma(a: seq<nat>, i: nat)
    requires 0 <= i < |a|
    ensures total(a[0..i+1]) == total(a[0..i]) + a[i]
{
    var s := a[0..i+1];
    if i == 0 {
        assert s == [a[0]];
        assert total(s) == total([]) + a[0] == 0 + a[0] == a[0];
        assert total(a[0..i]) == total(a[0..0]) == total([]) == 0;
        assert total(a[0..i]) + a[i] == 0 + a[0] == a[0];
    } else {
        assert s == a[0..i+1];
        assert |s| == i + 1;
        assert s[|s|-1] == s[i] == a[i];
        assert s[0..|s|-1] == a[0..i];
        
        calc {
            total(a[0..i+1]);
        == { assert a[0..i+1] == s; }
            total(s);
        == { assert |s| > 0; }
            total(s[0..|s|-1]) + s[|s|-1];
        == { assert s[0..|s|-1] == a[0..i] && s[|s|-1] == a[i]; }
            total(a[0..i]) + a[i];
        }
    }
}