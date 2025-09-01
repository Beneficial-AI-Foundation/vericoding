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
method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
{
  assume{:axiom} false;
}

// <vc-helpers>
function iterate_to_odd(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) % 2 == 1
{
  if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd(n / 2)
}

predicate is_sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function insert_sorted(s: seq<int>, x: int): seq<int>
  requires is_sorted(s)
  ensures is_sorted(insert_sorted(s, x))
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + insert_sorted(s[1..], x)
}
// </vc-helpers>

// <vc-spec>
method get_odd_collatz(n: nat) returns (sorted: seq<int>)
  decreases *
  requires n > 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
// </vc-spec>
// <vc-code>
{
  var next_odd: nat;
  var rest: seq<int>;

  if n % 2 == 0 {
    next_odd := n / 2;
    while next_odd % 2 == 0 {
      next_odd := next_odd / 2;
    }
  } else {
    next_odd := 3 * n + 1;
    while next_odd % 2 == 0 {
      next_odd := next_odd / 2;
    }
  }

  if next_odd == 1 {
    rest := [1];
  } else {
    rest := get_odd_collatz(next_odd);
  }

  if n % 2 == 0 {
    return rest;
  } else {
    return insert_sorted(rest, n as int);
  }
}
// </vc-code>

