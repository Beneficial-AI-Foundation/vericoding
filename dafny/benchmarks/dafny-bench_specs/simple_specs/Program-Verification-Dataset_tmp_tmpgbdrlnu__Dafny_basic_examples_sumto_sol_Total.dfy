//ATOM

function total (a: seq<nat>) : nat
{
 if |a| == 0 then 0
 else total (a[0..|a|-1]) + a[|a|-1]
}


// SPEC

method Total (a: seq<nat>) returns (r:nat)
 ensures r == total (a[0..|a|]); 
{
}
