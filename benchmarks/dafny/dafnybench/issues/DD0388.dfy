// <vc-preamble>
function sum_up_to (n: nat): nat
{
  if (n == 0) then 0
  else sum_up_to (n-1) + 1
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method SumUpTo (n: nat) returns (r: nat)
  ensures r == sum_up_to (n);
// </vc-spec>
// <vc-code>
{
  var i := 0;
  r := 0;
  while (i < n)
    invariant 0 <= i <= n;
    invariant r == sum_up_to (i);
  {
    r := r + 1;
    i := i + 1;
  }
}
// </vc-code>

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