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
lemma sum_property(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures sum(s[..i]) + sum(s[i..]) == sum(s)
{
  if |s| == 0 {
    assert s[..0] == [];
    assert s[0..] == [];
    assert sum([]) == 0;
  } else if i == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
    assert sum([]) == 0;
    assert sum(s[..0]) + sum(s[0..]) == 0 + sum(s) == sum(s);
  } else if i == |s| {
    assert s[..|s|] == s;
    assert s[|s|..] == [];
    assert sum(s[|s|..]) == sum([]) == 0;
    assert sum(s[..|s|]) + sum(s[|s|..]) == sum(s) + 0 == sum(s);
  } else {
    // Recursive case: prove by induction
    assert s == [s[0]] + s[1..];
    assert s[..i] == [s[0]] + s[1..][..i-1];
    assert s[i..] == s[1..][i-1..];
    sum_property(s[1..], i - 1);
    assert sum(s[1..][..i-1]) + sum(s[1..][i-1..]) == sum(s[1..]);
    assert sum(s[..i]) == s[0] + sum(s[1..][..i-1]);
    assert sum(s[..i]) + sum(s[i..]) == s[0] + sum(s[1..][..i-1]) + sum(s[1..][i-1..]);
    assert sum(s[..i]) + sum(s[i..]) == s[0] + sum(s[1..]);
    assert sum(s) == s[0] + sum(s[1..]);
  }
}

lemma sum_append(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
    sum_append(s1[1..], s2);
  }
}

lemma select_property(arr: seq<int>, i: int)
  requires 0 <= i <= |arr| <= 100
  ensures select_at_most_two_digits_rec(arr[..i]) + select_at_most_two_digits_rec(arr[i..]) == 
          select_at_most_two_digits_rec(arr[..i]) + select_at_most_two_digits_rec(arr[i..])
{
  // Trivial lemma for establishing context
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
  var filtered := select_at_most_two_digits(arr[..k]);
  s := 0;
  var i := 0;
  
  while i < |filtered|
    invariant 0 <= i <= |filtered|
    invariant s == sum(filtered[..i])
    invariant filtered == select_at_most_two_digits_rec(arr[..k])
  {
    s := s + filtered[i];
    assert filtered[..i+1] == filtered[..i] + [filtered[i]];
    sum_append(filtered[..i], [filtered[i]]);
    assert sum(filtered[..i+1]) == sum(filtered[..i]) + sum([filtered[i]]);
    assert sum([filtered[i]]) == filtered[i];
    assert sum(filtered[..i+1]) == s;
    i := i + 1;
  }
  
  assert filtered[..|filtered|] == filtered;
  assert s == sum(filtered);
}
// </vc-code>

