/*
Given n types of pebbles with w_i pebbles of type i, and a person with 2 pockets 
that can each hold at most k pebbles, find the minimum number of days needed to 
collect all pebbles. Different pebble types cannot be mixed in the same pocket, 
both pockets can be used simultaneously on the same day, and each pebble type 
must be collected completely.
*/

predicate ValidInput(n: int, k: int, w: seq<int>)
{
    k > 0 && n >= 0 && |w| == n && forall i :: 0 <= i < |w| ==> w[i] >= 0
}

function sum_trips(w: seq<int>, k: int): int
    requires k > 0
    requires forall i :: 0 <= i < |w| ==> w[i] >= 0
    ensures sum_trips(w, k) >= 0
{
    if |w| == 0 then 0
    else (w[0] + k - 1) / k + sum_trips(w[1..], k)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, w: seq<int>) returns (result: int)
    requires ValidInput(n, k, w)
    ensures result >= 0
    ensures result == (sum_trips(w, k) + 1) / 2
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
