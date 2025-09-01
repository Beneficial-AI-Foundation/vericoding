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
function iterate_to_odd_helper(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd_helper(n) % 2 == 1
{
  if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd_helper(n / 2)
}

function next_odd_collatz_helper(n: nat): nat
  requires n > 0
{
  if n % 2 == 0 then iterate_to_odd_helper(n) else iterate_to_odd_helper(3 * n + 1)
}

method iterate_to_odd_iter(n: nat) returns (res: nat)
  requires n % 2 == 0
  requires n > 0
  ensures res % 2 == 1
  ensures res == iterate_to_odd_helper(n)
{
  var current_n := n;
  while current_n % 2 == 0 && (current_n / 2) % 2 != 1
    invariant current_n % 2 == 0
    invariant current_n > 0
    invariant current_n == n || iterate_to_odd_helper(current_n) == iterate_to_odd_helper(n)
  {
    current_n := current_n / 2;
  }
  res := current_n / 2;
}

method next_odd_collatz_iter(n: nat) returns (next: nat)
  requires n > 0
  ensures next % 2 == 1
  ensures next == next_odd_collatz_helper(n)
{
  if n % 2 == 0 {
    next := iterate_to_odd_iter(n);
  } else {
    next := iterate_to_odd_iter(3 * n + 1);
  }
}

method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases n
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz_helper(odd_collatz[i - 1])
  ensures n in odd_collatz || n % 2 != 1
{
  var current_n := n;
  var path: seq<nat> := [];

  if current_n % 2 == 1 {
    path := [current_n];
  } else {
    var first_odd_val := iterate_to_odd_iter(current_n);
    path := [first_odd_val];
    current_n := first_odd_val; // For the subsequent next_odd_collatz_helper calls
  }

  while current_n != 1
    decreases current_n
    invariant forall i :: 0 <= i < |path| ==> path[i] % 2 == 1
    invariant forall i :: 1 <= i < |path| ==> path[i] == next_odd_collatz_helper(path[i-1])
    invariant current_n == path[|path|-1]
  {
    var next_val := next_odd_collatz_iter(current_n);
    path := path + [next_val];
    current_n := next_val;
  }
  odd_collatz := path;
}

function multiset_from_seq(s: seq<int>): multiset<int>
{
  if |s| == 0 then multiset{} else multiset{s[0]} + multiset_from_seq(s[1..])
}

predicate is_permutation_multiset<T>(s1: seq<T>, s2: seq<T>)
{
  multiset_from_seq(s1) == multiset_from_seq(s2)
}

method merge_sorted_sequences(a: seq<int>, b: seq<int>) returns (c: seq<int>)
  requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
  requires forall i, j :: 0 <= i < j < |b| ==> b[i] <= b[j]
  ensures forall i, j :: 0 <= i < j < |c| ==> c[i] <= c[j]
  ensures is_permutation_multiset(a + b, c)
{
  var result: seq<int> := [];
  var i := 0;
  var j := 0;

  while i < |a| || j < |b|
  {
    if i < |a| && (j == |b| || a[i] <= b[j]) {
      result := result + [a[i]];
      i := i + 1;
    } else if j < |b| {
      result := result + [b[j]];
      j := j + 1;
    }
  }
  return result;
}

method mergesort(s: seq<int>) returns (sorted_s: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted_s| ==> sorted_s[i] <= sorted_s[j]
  ensures is_permutation_multiset(s, sorted_s)
  decreases |s|
{
  if |s| <= 1 {
    sorted_s := s;
  } else {
    var mid := |s| / 2;
    var left := s[0..mid];
    var right := s[mid..];
    var sorted_left := mergesort(left);
    var sorted_right := mergesort(right);
    sorted_s := merge_sorted_sequences(sorted_left, sorted_right);
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
  var unsorted_path := get_odd_collatz_unsorted(n);
  // Convert seq<nat> to seq<int> for sorting
  var int_path: seq<int> := [];
  for i := 0 to |unsorted_path| - 1 {
    int_path := int_path + [unsorted_path[i] as int];
  }
  sorted := mergesort(int_path);
}
// </vc-code>

