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
method next_odd_collatz_iter(n: nat) returns (next: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma iterate_to_odd_property(n: nat)
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) % 2 == 1
{
  if (n / 2) % 2 == 1 {
  } else {
    calc {
      iterate_to_odd(n);
    ==  // def. iterate_to_odd
      iterate_to_odd(n / 2);
    ==  { iterate_to_odd_property(n / 2); }
      // ensures
      _;
    }
  }
}

lemma next_odd_collatz_property(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) % 2 == 1
{
  if n % 2 == 0 {
    calc {
      next_odd_collatz(n);
    ==  // def. next_odd_collatz
      iterate_to_odd(n);
    ==  { iterate_to_odd_property(n); }
      // ensures
      _;
    }
  } else {
    calc {
      iterate_to_odd(3 * n + 1);
    ==  { iterate_to_odd_property(3 * n + 1); }
      // ensures
      _;
    }
  }
}

lemma next_odd_collatz_consistent(n: nat) returns (next: nat)
  requires n > 0
  ensures next == next_odd_collatz(n)
  ensures next % 2 == 1
{
  if n % 2 == 0 {
    next := iterate_to_odd(n);
    calc {
      next;
    ==  // iterate_to_odd is deterministic
      iterate_to_odd(n);
    ==  // def. next_odd_collatz
      next_odd_collatz(n);
    }
  } else {
    next := iterate_to_odd(3 * n + 1);
    calc {
      next;
    ==  // iterate_to_odd is deterministic
      iterate_to_odd(3 * n + 1);
    ==  // def. next_odd_collatz
      next_odd_collatz(n);
    }
  }
  next_odd_collatz_property(n);
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
  if n == 2 {
    return [1];
  } else {
    var prev := get_odd_collatz_unsorted(n / 2);
    var head := if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd(n / 2);
    var tail := if |prev| == 0 || prev[0] != head then [head] + prev else prev;
    return tail;
  }
}
// </vc-code>

method get_odd_collatz(n: nat) returns (sorted: seq<int>)
  decreases *
  requires n > 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
{
  assume{:axiom} false;
}