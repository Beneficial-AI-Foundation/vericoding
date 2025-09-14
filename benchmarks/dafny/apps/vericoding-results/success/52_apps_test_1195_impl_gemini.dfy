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
lemma LemmaMinIsMinOfSequence(s: seq<int>, min_val: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 32
  requires min_val in s
  requires forall i :: 0 <= i < |s| ==> min_val <= s[i]
  ensures min_val == min_of_sequence(s)
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
    decreases |lst| - i
    invariant 1 <= i <= |lst|
    invariant 1 <= min_val <= 32
    invariant min_val in lst[..i]
    invariant forall k :: 0 <= k < i ==> min_val <= lst[k]
  {
    if lst[i] < min_val {
      min_val := lst[i];
    }
    i := i + 1;
  }
  
  LemmaMinIsMinOfSequence(lst, min_val);
  
  result := 2 + int_xor(lst[2], min_val);
}
// </vc-code>

