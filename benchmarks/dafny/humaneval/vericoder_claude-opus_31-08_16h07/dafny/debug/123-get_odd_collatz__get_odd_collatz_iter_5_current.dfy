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
method sort_sequence(s: seq<nat>) returns (sorted: seq<nat>)
  ensures |sorted| == |s|
  ensures multiset(sorted) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
  if |s| == 0 {
    return [];
  }
  
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(sorted) == multiset(s)
    invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> sorted[j] <= sorted[k]
  {
    var minIndex := i;
    var j := i + 1;
    while j < |sorted|
      invariant i < j <= |sorted|
      invariant i <= minIndex < |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];
    }
    
    i := i + 1;
  }
}

lemma MultisetPreservesOddness(s: seq<nat>, sorted: seq<nat>)
  requires multiset(sorted) == multiset(s)
  requires forall i :: 0 <= i < |s| ==> s[i] % 2 == 1
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
{
  forall i | 0 <= i < |sorted|
    ensures sorted[i] % 2 == 1
  {
    assert sorted[i] in multiset(sorted);
    assert sorted[i] in multiset(s);
    var j :| 0 <= j < |s| && s[j] == sorted[i] && sorted[i] in multiset(s);
    assert s[j] % 2 == 1;
  }
}

function SeqNatToSeqInt(s: seq<nat>): seq<int>
{
  seq(|s|, i requires 0 <= i < |s| => s[i] as int)
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
  var sorted_nat := sort_sequence(unsorted);
  
  MultisetPreservesOddness(unsorted, sorted_nat);
  
  sorted := SeqNatToSeqInt(sorted_nat);
}
// </vc-code>

