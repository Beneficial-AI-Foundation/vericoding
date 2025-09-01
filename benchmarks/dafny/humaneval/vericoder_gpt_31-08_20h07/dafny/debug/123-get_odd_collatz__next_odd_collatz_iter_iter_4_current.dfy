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
lemma mod2_nonzero_is_one(n: nat)
  ensures (n % 2 != 0) ==> n % 2 == 1
{
  if n % 2 != 0 {
    assert 2 > 0;
    assert 0 <= n % 2;
    assert n % 2 < 2;
    assert n % 2 > 0;
    assert n % 2 == 1;
  }
}

lemma next_odd_collatz_is_odd(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) % 2 == 1
{
  if n % 2 == 0 {
    assert next_odd_collatz(n) == iterate_to_odd(n);
    assert iterate_to_odd(n) % 2 == 1;
  } else {
    assert n % 2 != 0;
    mod2_nonzero_is_one(n);
    assert n % 2 == 1;

    var k := n / 2;
    assert n == 2 * k + n % 2;
    assert n == 2 * k + 1;

    assert 3 * n + 1 == 3 * (2 * k + 1) + 1;
    assert 3 * n + 1 == 6 * k + 4;
    assert 3 * n + 1 == 2 * (3 * k + 2);
    assert (3 * n + 1) % 2 == (2 * (3 * k + 2)) % 2;
    assert (2 * (3 * k + 2)) % 2 == 0;
    assert 3 * n + 1 > 0;

    assert next_odd_collatz(n) == iterate_to_odd(3 * n + 1);
    assert iterate_to_odd(3 * n + 1) % 2 == 1;
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
  next := next_odd_collatz(n);
  next_odd_collatz_is_odd(n);
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