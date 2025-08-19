function total (a: seq<nat>) : nat
{
 if |a| == 0 then 0
 else total (a[0..|a|-1]) + a[|a|-1]
}


//IMPL 

method Total (a: seq<nat>) returns (r:nat)
 /* code modified by LLM (iteration 1): removed deprecated semicolon */
 ensures r == total (a[0..|a|])
{
    r := 0;
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant r == total(a[0..i])
    {
        /* code modified by LLM (iteration 1): added assertion to help prove invariant maintenance */
        assert a[0..i+1] == a[0..i] + [a[i]];
        assert total(a[0..i+1]) == total(a[0..i]) + a[i];
        r := r + a[i];
        i := i + 1;
    }
}