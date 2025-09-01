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
lemma seq_nat_to_int_preserves_odd(s: seq<nat>)
  requires forall i :: 0 <= i < |s| ==> s[i] % 2 == 1
  ensures forall i :: 0 <= i < |s| ==> (s[i] as int) % 2 == 1
{
}

method sort_sequence(s: seq<int>) returns (sorted: seq<int>)
  ensures multiset(s) == multiset(sorted)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] in s
{
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant multiset(s) == multiset(sorted)
    invariant |sorted| == |s|
    invariant forall k, l :: 0 <= k < l < i ==> sorted[k] <= sorted[l]
  {
    var j := i;
    while j > 0 && sorted[j-1] > sorted[j]
      invariant 0 <= j <= i
      invariant multiset(s) == multiset(sorted)
      invariant |sorted| == |s|
      invariant forall k, l :: 0 <= k < l < i && l != j ==> sorted[k] <= sorted[l]
    {
      sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
      j := j - 1;
    }
    i := i + 1;
  }
}

function seq_nat_to_int(s: seq<nat>): seq<int>
{
  if |s| == 0 then [] else [s[0] as int] + seq_nat_to_int(s[1..])
}

lemma seq_nat_to_int_length(s: seq<nat>)
  ensures |seq_nat_to_int(s)| == |s|
{
  if |s| == 0 {
  } else {
    seq_nat_to_int_length(s[1..]);
  }
}

lemma seq_nat_to_int_elements(s: seq<nat>)
  ensures forall i :: 0 <= i < |s| ==> seq_nat_to_int(s)[i] == s[i] as int
{
  if |s| == 0 {
  } else {
    seq_nat_to_int_elements(s[1..]);
  }
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
  var odd_collatz_nat := get_odd_collatz_unsorted(n);
  var odd_collatz_int := seq_nat_to_int(odd_collatz_nat);
  
  seq_nat_to_int_length(odd_collatz_nat);
  seq_nat_to_int_elements(odd_collatz_nat);
  seq_nat_to_int_preserves_odd(odd_collatz_nat);
  
  sorted := sort_sequence(odd_collatz_int);
}
// </vc-code>

