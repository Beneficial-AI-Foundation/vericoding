

// <vc-helpers>
function is_sorted_predicate(a: seq<int>): bool
  reads a
{
  (forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]) &&
  (forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2)
}

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// </vc-helpers>

// <vc-spec>
method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |a| <= 1 then
    return true;
  else
    var i := 0;
    while i < |a| - 1
      invariant 0 <= i < |a|
      invariant forall k, l :: 0 <= k <= l <= i ==> a[k] <= a[l]
      invariant forall k :: 0 <= k <= i && (k == 0 || a[k-1] < a[k] || a[k-1] == a[k]) ==> count_set(a, a[k]) <= 2
    {
      if a[i] > a[i+1] then
        return false;
      
      // Before incrementing i, check the count for a[i] if this is the first occurrence of a distinct element
      // or if consecutive identical elements exceed count 2.
      // This is now handled by the loop invariant.
      // The invariant `forall k :: 0 <= k <= i && (k == 0 || a[k-1] < a[k] || a[k-1] == a[k]) ==> count_set(a, a[k]) <= 2`
      // checks elements up to current `i`.

      i := i + 1;

      // After incrementing i, the element a[i-1] has been included in the prefix up to i-1.
      // Now a[i] is considered. If a[i-1] != a[i], it means a new distinct element is encountered.
      // The invariant already takes care of this: when i is incremented, the invariant is re-evaluated for the new i.
      // If a[i] is a new distinct element (a[i-1] < a[i]), then count_set(a, a[i]) must be <= 2.
      // If a[i] is the same as a[i-1], the count will be implicitly checked.
      var current_val_occurrence_count := 0;
      var j := 0;
      while j <= i
        invariant 0 <= j <= i + 1
        invariant current_val_occurrence_count == |set k | 0 <= k < j && a[k] == a[i-1]|
      {
        if a[j] == a[i-1] then
          current_val_occurrence_count := current_val_occurrence_count + 1;
        j := j + 1;
      }
      if current_val_occurrence_count > 2 then
        return false;
    }
    
    // After the loop, the loop invariant guarantees properties up to index |a|-1.
    // So the sorted property and count property are already checked for all elements.
    // The previous code had a separate check for the last element, which is already covered by the loop invariant.
    // We can directly return true if the loop completes.
    
    // Explicitly confirm the last element's count after the loop
    if |a| > 0 { // Only check if the sequence is not empty
        var last_element_count := 0;
        var k := 0;
        while k < |a|
            invariant 0 <= k <= |a|
            invariant last_element_count == |set l | 0 <= l < k && a[l] == a[|a|-1]|
        {
            if a[k] == a[|a|-1] then
                last_element_count := last_element_count + 1;
            k := k + 1;
        }
        if last_element_count > 2 then
            return false;
    }

    return true;
}
// </vc-code>

method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)
  // pre-conditions-start
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  // pre-conditions-end
  // post-conditions-start
  ensures count == count_set(a, x)
  // post-conditions-end
{
  assume{:axiom} false;
}
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end