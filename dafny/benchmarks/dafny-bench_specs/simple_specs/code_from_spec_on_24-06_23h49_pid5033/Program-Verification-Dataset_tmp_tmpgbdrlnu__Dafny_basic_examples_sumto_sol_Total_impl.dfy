//ATOM
function total (a: seq<nat>) : nat
{
 if |a| == 0 then 0
 else total (a[0..|a|-1]) + a[|a|-1]
}

//IMPL Total
method Total (a: seq<nat>) returns (r:nat)
 ensures r == total (a[0..|a|]); 
{
    /* code modified by LLM (iteration 1): changed total(a) to total(a[0..|a|]) to match the postcondition exactly */
    r := total(a[0..|a|]);
}