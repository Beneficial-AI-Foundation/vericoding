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

function next_odd_collatz(n: nat): nat
  requires n > 0
{
  if n % 2 == 0 then iterate_to_odd(n) else iterate_to_odd(3 * n + 1)
}

method next_odd_collatz_iter(n: nat) returns (next: nat)
  requires n > 0
  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
{
  if n % 2 == 0 {
    var temp := n / 2;
    while temp % 2 == 0
      invariant temp > 0
      invariant n % 2 == 0
      invariant next_odd_collatz(n) == iterate_to_odd(n)
    {
      temp := temp / 2;
    }
    next := temp;
  } else {
    var temp := 3 * n + 1;
    while temp % 2 == 0
      invariant temp > 0
      invariant n % 2 == 1
      invariant next_odd_collatz(n) == iterate_to_odd(3 * n + 1)
    {
      temp := temp / 2;
    }
    next := temp;
  }
}

method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
{
  if n == 1 {
    return [1];
  }
  var next := next_odd_collatz(n);
  var rest := get_odd_collatz_unsorted(next);
  return [n] + rest;
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
  if n == 1 {
    return [1];
  }
  var next := next_odd_collatz(n);
  var rest := get_odd_collatz(next);
  return insert_sorted(rest, n as int);
}
// </vc-code>

