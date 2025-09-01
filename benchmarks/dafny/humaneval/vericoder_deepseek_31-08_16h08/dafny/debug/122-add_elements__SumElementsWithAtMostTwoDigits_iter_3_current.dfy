function sum(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function select_at_most_two_digits_rec(arr: seq<int>): seq<int>
  requires |arr| >= 0 && |arr| <= 100
{
  if |arr| == 0 then []
  else if 0 <= arr[0] < 100 then [arr[0]] + select_at_most_two_digits_rec(arr[1..])
  else select_at_most_two_digits_rec(arr[1..])
}
method select_at_most_two_digits(arr: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |arr| > 0 && |arr| <= 100
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] < 100
  ensures forall i :: 0 <= i < |result| ==> result[i] in arr
  ensures result == select_at_most_two_digits_rec(arr)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma sum_append(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    calc {
      sum(s1 + s2);
      == { assert |s1 + s2| > 0; }
      (s1 + s2)[0] + sum((s1 + s2)[1..]);
      == { assert (s1 + s2)[0] == s1[0]; }
      s1[0] + sum((s1 + s2)[1..]);
      == { assert (s1 + s2)[1..] == s1[1..] + s2; }
      s1[0] + sum(s1[1..] + s2);
      == { sum_append(s1[1..], s2); }
      s1[0] + (sum(s1[1..]) + sum(s2));
      == { assert sum(s1) == s1[0] + sum(s1[1..]); }
      sum(s1) + sum(s2);
    }
  }
}

lemma sum_empty()
  ensures sum([]) == 0
{
}

lemma select_rec_append(arr1: seq<int>, arr2: seq<int>)
  requires |arr1| >= 0 && |arr1| <= 100
  requires |arr2| >= 0 && |arr2| <= 100
  ensures select_at_most_two_digits_rec(arr1 + arr2) == select_at_most_two_digits_rec(arr1) + select_at_most_two_digits_rec(arr2)
{
  if |arr1| == 0 {
    assert arr1 + arr2 == arr2;
  } else {
    if 0 <= arr1[0] < 100 {
      calc {
        select_at_most_two_digits_rec(arr1 + arr2);
        ==
        [arr1[0]] + select_at_most_two_digits_rec((arr1 + arr2)[1..]);
        == { assert (arr1 + arr2)[1..] == arr1[1..] + arr2; }
        [arr1[0]] + select_at_most_two_digits_rec(arr1[1..] + arr2);
        == { select_rec_append(arr1[1..], arr2); }
        [arr1[0]] + (select_at_most_two_digits_rec(arr1[1..]) + select_at_most_two_digits_rec(arr2));
        ==
        ([arr1[0]] + select_at_most_two_digits_rec(arr1[1..])) + select_at_most_two_digits_rec(arr2);
        ==
        select_at_most_two_digits_rec(arr1) + select_at_most_two_digits_rec(arr2);
      }
    } else {
      calc {
        select_at_most_two_digits_rec(arr1 + arr2);
        ==
        select_at_most_two_digits_rec((arr1 + arr2)[1..]);
        == { assert (arr1 + arr2)[1..] == arr1[1..] + arr2; }
        select_at_most_two_digits_rec(arr1[1..] + arr2);
        == { select_rec_append(arr1[1..], arr2); }
        select_at_most_two_digits_rec(arr1[1..]) + select_at_most_two_digits_rec(arr2);
        ==
        select_at_most_two_digits_rec(arr1) + select_at_most_two_digits_rec(arr2);
      }
    }
  }
}

lemma select_rec_prefix(arr: seq<int>, k: int)
  requires |arr| >= 0 && |arr| <= 100
  requires 0 <= k <= |arr|
  ensures select_at_most_two_digits_rec(arr[..k]) + select_at_most_two_digits_rec(arr[k..]) == select_at_most_two_digits_rec(arr)
{
  assert arr[..k] + arr[k..] == arr;
  select_rec_append(arr[..k], arr[k..]);
}

lemma select_rec_length_bound(arr: seq<int>, k: int)
  requires |arr| >= 0 && |arr| <= 100
  requires 0 <= k <= |arr|
  ensures |arr[..k]| <= 100 && |arr[k..]| <= 100
{
}
// </vc-helpers>

// <vc-spec>
method SumElementsWithAtMostTwoDigits(arr: seq<int>, k: int) returns (s: int)
  // pre-conditions-start
  requires |arr| > 0 && |arr| <= 100
  requires 1 <= k <= |arr|
  // pre-conditions-end
  // post-conditions-start
  ensures var two_digits := select_at_most_two_digits_rec(arr[..k]);
          s == sum(two_digits)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if k == 1 {
    if 0 <= arr[0] < 100 {
      s := arr[0];
    } else {
      s := 0;
    }
  } else {
    var rest := SumElementsWithAtMostTwoDigits(arr, k - 1);
    var two_digits_prefix := select_at_most_two_digits_rec(arr[..k-1]);
    var two_digits_suffix := select_at_most_two_digits_rec(arr[k-1..k]);
    assert two_digits_prefix + two_digits_suffix == select_at_most_two_digits_rec(arr[..k]);
    assert sum(two_digits_prefix + two_digits_suffix) == sum(two_digits_prefix) + sum(two_digits_suffix);
    
    if 0 <= arr[k-1] < 100 {
      s := rest + arr[k-1];
    } else {
      s := rest;
    }
  }
}
// </vc-code>

