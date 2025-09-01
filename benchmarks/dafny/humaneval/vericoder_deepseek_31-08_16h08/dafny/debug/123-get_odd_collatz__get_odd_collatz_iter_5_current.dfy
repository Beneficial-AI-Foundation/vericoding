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
lemma SortedProof(seq: seq<int>, idx: int)
  requires 0 <= idx < |seq|
  ensures forall i, j :: 0 <= i <= idx && idx <= j < |seq| ==> seq[i] <= seq[j]
{
  if idx > 0 {
    SortedProof(seq, idx - 1);
  }
}

lemma SortedLemma(seq: seq<int>)
  ensures forall i, j :: 0 <= i < j < |seq| ==> seq[i] <= seq[j] 
  decreases |seq|
{
  if |seq| > 0 {
    SortedProof(seq, |seq| - 1);
  }
}

lemma InsertSortedLemma(seq: seq<int>, x: int, idx: nat)
  requires forall i, j :: 0 <= i < j < |seq| ==> seq[i] <= seq[j]
  requires 0 <= idx <= |seq|
  requires (idx == 0 ==> |seq| == 0 || x <= seq[0])
  requires (idx == |seq| ==> |seq| == 0 || seq[|seq|-1] <= x)
  requires (0 < idx && idx < |seq| ==> seq[idx-1] <= x && x <= seq[idx])
  ensures forall i, j :: 0 <= i < j < |seq[..idx] + [x] + seq[idx..]| ==> (seq[..idx] + [x] + seq[idx..])[i] <= (seq[..idx] + [x] + seq[idx..])[j]
{
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
  var unsorted := get_odd_collatz_unsorted(n);
  sorted := [];
  
  var i := 0;
  while i < |unsorted|
    invariant |sorted| == i
    invariant forall k, l :: 0 <= k < l < i ==> sorted[k] <= sorted[l]
    invariant forall k :: 0 <= k < i ==> sorted[k] % 2 == 1
  {
    var x := unsorted[i];
    var j := 0;
    
    while j < |sorted| && sorted[j] < x
      invariant 0 <= j <= |sorted|
      invariant forall k :: 0 <= k < j ==> sorted[k] < x
      invariant forall k :: j <= k < |sorted| ==> sorted[k] >= x
    {
      j := j + 1;
    }
    
    sorted := sorted[..j] + [x] + sorted[j..];
    i := i + 1;
  }
  
  SortedLemma(sorted);
}
// </vc-code>

