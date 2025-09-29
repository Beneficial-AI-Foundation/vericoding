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

// </vc-helpers>

// <vc-spec>
method solve(lst: seq<int>) returns (result: int)
  requires ValidInput(lst)
  ensures result == 2 + int_xor(lst[2], min_of_sequence(lst))
// </vc-spec>
// <vc-code>
{
  var min_val := min_of_sequence(lst);
  result := 2 + int_xor(lst[2], min_val);
}
// </vc-code>

