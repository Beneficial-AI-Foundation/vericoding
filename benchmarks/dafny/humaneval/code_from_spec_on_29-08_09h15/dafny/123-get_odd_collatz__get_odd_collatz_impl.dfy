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
lemma odd_collatz_properties(odd_collatz: seq<nat>)
  requires forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] as int % 2 == 1
{
}

lemma multiset_remove_element<T>(s: seq<T>, idx: int)
  requires 0 <= idx < |s|
  ensures multiset(s[..idx] + s[idx + 1..]) + multiset([s[idx]]) == multiset(s[..])
{
  assert s[..] == s[..idx] + [s[idx]] + s[idx + 1..];
  assert multiset(s[..]) == multiset(s[..idx] + [s[idx]] + s[idx + 1..]);
  assert multiset(s[..idx] + [s[idx]] + s[idx + 1..]) == multiset(s[..idx]) + multiset([s[idx]]) + multiset(s[idx + 1..]);
  assert multiset(s[..idx] + s[idx + 1..]) == multiset(s[..idx]) + multiset(s[idx + 1..]);
}

method sort_sequence(s: seq<nat>) returns (sorted: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] % 2 == 1
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(sorted) == multiset(s[..]) 
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
{
  var temp := s[..];
  var result: seq<int> := [];
  
  while |temp| > 0
    invariant forall i :: 0 <= i < |temp| ==> temp[i] % 2 == 1
    invariant forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    invariant forall i :: 0 <= i < |result| ==> result[i] % 2 == 1
    invariant multiset(result) + multiset(temp) == multiset(s[..])
    invariant |result| + |temp| == |s|
  {
    var min_idx := 0;
    var min_val := temp[0];
    
    for i := 1 to |temp|
      invariant 0 <= min_idx < |temp|
      invariant min_val == temp[min_idx]
      invariant forall j :: 0 <= j < i ==> temp[min_idx] <= temp[j]
    {
      if temp[i] < min_val {
        min_idx := i;
        min_val := temp[i];
      }
    }
    
    assert min_val % 2 == 1;
    assert forall j :: 0 <= j < |temp| ==> min_val <= temp[j];
    
    var old_temp := temp;
    result := result + [min_val as int];
    temp := temp[..min_idx] + temp[min_idx + 1..];
    
    multiset_remove_element(old_temp, min_idx);
    assert multiset(temp) + multiset([min_val]) == multiset(old_temp);
  }
  
  sorted := result;
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method get_odd_collatz(n: nat) returns (sorted: seq<int>)
Retrieve elements. Requires: requires n > 1. Ensures: the result is sorted according to the ordering relation; the result is sorted according to the ordering relation.
*/
// </vc-description>

// <vc-spec>
method get_odd_collatz(n: nat) returns (sorted: seq<int>)
  decreases *
  requires n > 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
// </vc-spec>

// <vc-code>
{
  var odd_collatz := get_odd_collatz_unsorted(n);
  odd_collatz_properties(odd_collatz);
  sorted := sort_sequence(odd_collatz);
}
// </vc-code>

