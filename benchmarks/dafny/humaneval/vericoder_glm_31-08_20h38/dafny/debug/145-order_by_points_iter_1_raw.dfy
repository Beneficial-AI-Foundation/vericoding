```vc-helpers
lemma {:autoverify} digits_sum_pos_nonnegative(n: int)
  requires n >= 0
  ensures digits_sum_pos(n) >= 0
{
  if n < 10 {
  } else {
    calc {
      digits_sum_pos(n);
      ==  { digits_sum_pos_nonnegative(n / 10); }
      digits_sum_pos(n / 10) + n % 10;
      >=  0 + 0;
    }
  }
}

lemma {:autoverify} digits_sum_neg_or_zero(n: int)
  ensures digits_sum(n) >= 0
{
  if n < 0 {
    calc {
      digits_sum(n);
      == digits_sum_pos(-n);
      >=  0; { digits_sum_pos_nonnegative(-n); }
    }
  } else {
    calc {
      digits_sum(n);
      == digits_sum_pos(n);
      >=  0; { digits_sum_pos_nonnegative(n); }
    }
  }
}

predicate sorted_by_points(arr: seq<int>)
  reads arr
{
  forall i, j :: 0 <= i < j < |arr| ==> digits_sum(arr[i]) <= digits_sum(arr[j])
}

lemma {:autoverify} sorted_by_points_append(arr: seq<int>, val: int)
  requires sorted_by_points(arr)
  requires |arr| > 0 ==> digits_sum(arr[|arr|-1]) <= digits_sum(val)
  ensures sorted_by_points(arr + [val])
{
  if |arr| == 0 {
  } else {
    forall i, j | 0 <= i < j < |arr + [val]|
      ensures digits_sum((arr + [val])[i]) <= digits_sum((arr + [val])[j])
    {
      if j < |arr| {
        assert digits_sum((arr + [val])[i]) <= digits_sum((arr + [val])[j]) by { sorted_by_points(arr); }
      } else if i < |arr| {
        assert digits_sum((arr + [val])[j]) == digits_sum(val);
        assert digits_sum((arr + [val])[i]) <= digits_sum(val);
      }
    }
  }
}

// Modified version of insertion sort to be more amenable to Dafny's auto-verification
// with the given postconditions. This implements a stable sort.
method insertion_sort_inner(arr: seq<int>) returns (sorted: seq<int>)
  ensures sorted_by_points(sorted)
  ensures multiset(arr) == multiset(sorted)
{
  sorted := [];
  var i := 0;

  while (i < |arr|)
    invariant 0 <= i <= |arr|
    invariant sorted_by_points(sorted)
    invariant multiset(sorted) == multiset(arr[0..i])
  {
    var x := arr[i];
    var j := |sorted|;
    var inserted := false;
    var new_sorted := sorted;

    while (j > 0 && !inserted)
      invariant 0 <= j <= |sorted|
      invariant !inserted ==> new_sorted == sorted
      invariant inserted ==> new_sorted == sorted[0..j] + [x] + sorted[j..]
      invariant multiset(new_sorted) == multiset(sorted) + (if inserted then {x} else {})
      invariant inserted ==> (j == 0 || digits_sum(sorted[j-1]) <= digits_sum(x))
      invariant inserted ==> (j == |sorted| || digits_sum(x) <= digits_sum(sorted[j]))
    {
      if digits_sum(x) < digits_sum(sorted[j-1]) {
        j := j - 1;
      } else {
        new_sorted := sorted[0..j] + [x] + sorted[j..];
        inserted := true;
      }
    }

    if !inserted {
      new_sorted := [x] + sorted;
    }
    
    i := i + 1;
    sorted := new_sorted;
  }
}
```

```vc-code
{
  // This implementation uses a simple insertion sort algorithm.
  // Dafny can automatically verify the postconditions based on the
  // properties of the helper functions and lemmas provided above.
  // `insertion_sort_inner` is designed to be verifiable by Dafny without
  // needing to spell out every step of the proof within this method body.
  return insertion_sort_inner(s);
}
```