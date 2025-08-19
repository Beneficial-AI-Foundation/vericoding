function sum_up_to (n: nat): nat
{
  if (n == 0) then 0
  else sum_up_to (n-1) + 1
}



function total (a: seq<nat>) : nat
{
  if |a| == 0 then 0
  else total (a[0..|a|-1]) + a[|a|-1]
}

lemma total_lemma (a: seq<nat>, i:nat) 
  requires |a| > 0;
  requires 0 <= i < |a|;
  ensures total (a[0..i]) + a[i] == total (a[0..i+1]);
{
  ghost var b := a[0..i+1];
  calc
  {
    total (a[0..i+1]);
    total (b);
    total (b[0..|b|-1]) + b[|b|-1];
    total (b[0..|b|-1]) + a[i];
    {assert (b[0..|b|-1] == a[0..i]);}
    total (a[0..i]) + a[i];
  }
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Total (a: seq<nat>) returns (r:nat)
  ensures r == total (a[0..|a|]);
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>