// <vc-preamble>
function iterate_to_odd(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) % 2 == 1
{
  if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd(n / 2)
}
function next_odd_collatz(n: nat): nat
  requires n > 0
{
  if n % 2 == 0 then iterate_to_odd(n) else iterate_to_odd(3 * n + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemma to prove current > 0 is maintained */
lemma CurrentPositive(n: nat)
  requires n > 1
  ensures n > 0
{
}

lemma NextPositive(current: nat)
  requires current > 0
  ensures next_odd_collatz(current) > 0
{
}
// </vc-helpers>

// <vc-spec>
method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed invariant and ensured current > 0 before calling next_odd_collatz */
  var current := n;
  odd_collatz := [];
  
  while current != 1
    decreases *
    invariant current > 0
    invariant forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
    invariant |odd_collatz| == 0 ==> current == n
    invariant |odd_collatz| > 0 ==> odd_collatz[|odd_collatz| - 1] == current
    invariant forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
  {
    assert current > 0;
    var next := next_odd_collatz(current);
    odd_collatz := odd_collatz + [next];
    current := next;
  }
}
// </vc-code>
