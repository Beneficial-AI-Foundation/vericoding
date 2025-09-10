predicate ValidInput(lst: seq<int>) {
  5 <= |lst| <= 10 &&
  forall i :: 0 <= i < |lst| ==> 1 <= lst[i] <= 32
}

function int_xor(a: int, b: int): int
  requires 1 <= a <= 32 && 1 <= b <= 32
{
  var a_bv := a as bv32;
  var b_bv := b as bv32;
  (a_bv ^ b_bv) as int
}

function min_of_sequence(s: seq<int>): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 32
  ensures 1 <= min_of_sequence(s) <= 32
  ensures min_of_sequence(s) in s
  ensures forall i :: 0 <= i < |s| ==> min_of_sequence(s) <= s[i]
{
  if |s| == 1 then s[0]
  else if s[0] <= min_of_sequence(s[1..]) then s[0]
  else min_of_sequence(s[1..])
}

// <vc-helpers>
lemma min_in_sequence(s: seq<int>, idx: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 32
  requires 0 <= idx < |s|
  ensures min_of_sequence(s) <= s[idx]
{
}

lemma min_is_first_or_in_tail(s: seq<int>)
  requires |s| > 1
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 32
  ensures min_of_sequence(s) == s[0] || min_of_sequence(s) in s[1..]
{
}

lemma min_of_subsequence(s: seq<int>, start: int, end: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 32
  requires 0 <= start <= end < |s|
  ensures min_of_sequence(s[start..end+1]) in s[start..end+1]
  ensures forall i :: start <= i <= end ==> min_of_sequence(s[start..end+1]) <= s[i]
{
}
// </vc-helpers>

// <vc-spec>
method solve(lst: seq<int>) returns (result: int)
  requires ValidInput(lst)
  ensures result == 2 + int_xor(lst[2], min_of_sequence(lst))
// </vc-spec>
// <vc-code>
{
  var min_val := lst[0];
  var i := 1;
  
  while i < |lst|
    invariant 1 <= i <= |lst|
    invariant min_val in lst[0..i]
    invariant forall j :: 0 <= j < i ==> min_val <= lst[j]
    invariant 1 <= min_val <= 32
  {
    if lst[i] < min_val {
      min_val := lst[i];
    }
    i := i + 1;
  }
  
  var xor_result := (lst[2] as bv32) ^ (min_val as bv32);
  result := 2 + (xor_result as int);
}
// </vc-code>

