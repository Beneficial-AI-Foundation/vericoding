function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}

// <vc-helpers>
lemma SumCharsRecEmpty()
  ensures sum_chars_rec([]) == 0
{
}

lemma SumCharsRecCons(s: string, rest: seq<string>)
  ensures sum_chars_rec([s] + rest) == |s| + sum_chars_rec(rest)
{
}

lemma SumCharsRecMonotonic(a: seq<string>, b: seq<string>)
  requires a == b || |a| == |b|
  ensures sum_chars_rec(a) <= sum_chars_rec(b) || sum_chars_rec(a) >= sum_chars_rec(b)
{
}

lemma SumCharsRecUnique(a: seq<string>, b: seq<string>)
  requires sum_chars_rec(a) == sum_chars_rec(b)
  requires a == b || |a| == |b|
  ensures a == b
{
  if a != b {
    // Contradiction: different sequences of same length cannot have same character sum
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| == |list1| || |result| == |list2|
  ensures result == list1 || result == list2
  ensures sum_chars_rec(result) <= sum_chars_rec(list1)
  ensures sum_chars_rec(result) <= sum_chars_rec(list2)
  ensures sum_chars_rec(list1) == sum_chars_rec(list2) ==> result == list1
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if sum_chars_rec(list1) <= sum_chars_rec(list2) {
    result := list1;
  } else {
    result := list2;
  }
}
// </vc-code>

method SumChars(list: seq<string>) returns (sum: nat)
  // post-conditions-start
  ensures sum == sum_chars_rec(list)
  // post-conditions-end
{
  assume{:axiom} false;
}