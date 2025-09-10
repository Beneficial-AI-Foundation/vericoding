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
function min_of_sequence_iterative(s: seq<int>): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 32
  ensures 1 <= min_of_sequence_iterative(s) <= 32
  ensures min_of_sequence_iterative(s) in s
  ensures forall i :: 0 <= i < |s| ==> min_of_sequence_iterative(s) <= s[i]
{
  var min_val := s[0];
  var i := 1;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 1 <= min_val <= 32
    invariant min_val in s[..i]
    invariant forall j :: 0 <= j < i ==> min_val <= s[j]
  {
    if s[i] < min_val {
      min_val := s[i];
    }
    i := i + 1;
  }
  return min_val;
}

lemma {:induction false} MinOfSequenceProperties(s: seq<int>)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> 1 <= s[i] <= 32
  ensures min_of_sequence(s) == min_of_sequence_iterative(s)
{
  if |s| == 1 {
    assert min_of_sequence(s) == s[0];
    assert min_of_sequence_iterative(s) == s[0];
  } else {
    // inductive step using the definitions
    if s[0] <= min_of_sequence(s[1..]) {
      // min_of_sequence(s) is s[0]
      // min_of_sequence_iterative(s) is min(s[0], min_of_sequence_iterative(s[1..]))
      // By induction hypothesis, min_of_sequence(s[1..]) == min_of_sequence_iterative(s[1..])
      // So s[0] <= min_of_sequence_iterative(s[1..])
      // Therefore min(s[0], min_of_sequence_iterative(s[1..])) is s[0]
      // Hence min_of_sequence(s) == min_of_sequence_iterative(s)
      MinOfSequenceProperties(s[1..]);
    } else {
      // min_of_sequence(s) is min_of_sequence(s[1..])
      // min_of_sequence_iterative(s) is min(s[0], min_of_sequence_iterative(s[1..]))
      // By induction hypothesis, min_of_sequence(s[1..]) == min_of_sequence_iterative(s[1..])
      // So s[0] > min_of_sequence_iterative(s[1..])
      // Therefore min(s[0], min_of_sequence_iterative(s[1..])) is min_of_sequence_iterative(s[1..])
      // Hence min_of_sequence(s) == min_of_sequence_iterative(s)
      MinOfSequenceProperties(s[1..]);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(lst: seq<int>) returns (result: int)
  requires ValidInput(lst)
  ensures result == 2 + int_xor(lst[2], min_of_sequence(lst))
// </vc-spec>
// <vc-code>
{
  var min_val_lst := min_of_sequence_iterative(lst);
  MinOfSequenceProperties(lst); // This lemma is needed to equate the two min_of_sequence functions
  var xor_val := int_xor(lst[2], min_val_lst);
  result := 2 + xor_val;
}
// </vc-code>

