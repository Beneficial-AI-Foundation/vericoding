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
function iterate_to_odd_helper(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd_helper(n) % 2 == 1
  decreases n
{
  if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd_helper(n / 2)
}

function next_odd_collatz_helper(n: nat): nat
  requires n > 0
  ensures next_odd_collatz_helper(n) % 2 == 1
  ensures next_odd_collatz_helper(n) < n || next_odd_collatz_helper(n) == 1 // For termination argument
{
  if n % 2 == 0 then iterate_to_odd_helper(n) else iterate_to_odd_helper(3 * n + 1)
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
  var collatz_sequence: seq<nat> := [];
  var current := n;

  // Add the initial odd number if 'n' is odd, or the result of next_odd_collatz_helper(n) if 'n' is even.
  // The first element of the sequence must be odd.
  if current % 2 == 1 {
    collatz_sequence := collatz_sequence + [current];
  } else {
    // If n is even, iterate it to an odd number
    collatz_sequence := collatz_sequence + [iterate_to_odd_helper(current)];
  }

  // Loop until the last element of the sequence becomes 1
  while collatz_sequence[|collatz_sequence|-1] != 1
    invariant |collatz_sequence| > 0
    invariant forall i :: 0 <= i < |collatz_sequence| ==> collatz_sequence[i] % 2 == 1
    invariant forall i :: 1 <= i < |collatz_sequence| ==> collatz_sequence[i] == next_odd_collatz_helper(collatz_sequence[i-1])
    decreases collatz_sequence[|collatz_sequence|-1]
  {
    var last_val := collatz_sequence[|collatz_sequence|-1];
    var next_val := next_odd_collatz_helper(last_val);
    collatz_sequence := collatz_sequence + [next_val];
  }

  return collatz_sequence;
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