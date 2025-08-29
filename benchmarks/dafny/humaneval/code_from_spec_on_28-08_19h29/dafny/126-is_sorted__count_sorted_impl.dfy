method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function count_occurrences(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}

lemma CountOccurrencesPrefix(a: seq<int>, x: int, i: int)
  requires 0 <= i <= |a|
  ensures count_occurrences(a[..i], x) == |set k | 0 <= k < i && a[k] == x|
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)
Count occurrences. Requires: the condition holds for all values; the size is bounded; returns the correct value; returns the correct size/count. Ensures: returns the correct value.
*/
// </vc-description>

// <vc-spec>
method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)
  requires 0 <= pos <= |a|
  ensures count == count_occurrences(a[..pos], x)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var temp_count := 0;
  while i < pos
    invariant 0 <= i <= pos
    invariant temp_count == count_occurrences(a[..i], x)
  {
    if a[i] == x {
      temp_count := temp_count + 1;
    }
    i := i + 1;
  }
  count := temp_count;
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end