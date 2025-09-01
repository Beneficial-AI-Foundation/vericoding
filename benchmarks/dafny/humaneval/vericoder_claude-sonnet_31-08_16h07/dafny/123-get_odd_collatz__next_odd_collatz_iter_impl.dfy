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

// <vc-helpers>
lemma iterate_to_odd_preserves_positivity(n: nat)
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) > 0
{
  if (n / 2) % 2 == 1 {
    assert n >= 2;
    assert n / 2 >= 1;
  } else {
    assert n >= 4;
    assert n / 2 >= 2;
    assert (n / 2) % 2 == 0;
    iterate_to_odd_preserves_positivity(n / 2);
  }
}

lemma next_odd_collatz_is_positive(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) > 0
{
  if n % 2 == 0 {
    iterate_to_odd_preserves_positivity(n);
  } else {
    assert 3 * n + 1 > 0;
    assert (3 * n + 1) % 2 == 0;
    iterate_to_odd_preserves_positivity(3 * n + 1);
  }
}
// </vc-helpers>

// <vc-spec>
method next_odd_collatz_iter(n: nat) returns (next: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  next_odd_collatz_is_positive(n);
  
  if n % 2 == 0 {
    var current := n;
    while current % 2 == 0
      invariant current > 0
      invariant current % 2 == 0 ==> iterate_to_odd(current) == iterate_to_odd(n)
      invariant current % 2 == 1 ==> current == iterate_to_odd(n)
      decreases current
    {
      current := current / 2;
    }
    next := current;
  } else {
    var temp := 3 * n + 1;
    var current := temp;
    while current % 2 == 0
      invariant current > 0
      invariant current % 2 == 0 ==> iterate_to_odd(current) == iterate_to_odd(temp)
      invariant current % 2 == 1 ==> current == iterate_to_odd(temp)
      decreases current
    {
      current := current / 2;
    }
    next := current;
  }
}
// </vc-code>

method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
{
  assume{:axiom} false;
}
method get_odd_collatz(n: nat) returns (sorted: seq<int>)
  decreases *
  requires n > 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
{
  assume{:axiom} false;
}