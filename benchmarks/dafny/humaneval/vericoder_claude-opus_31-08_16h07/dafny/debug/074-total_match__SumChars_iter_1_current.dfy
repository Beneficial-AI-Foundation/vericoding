function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}
method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| == |list1| || |result| == |list2|
  ensures result == list1 || result == list2
  ensures sum_chars_rec(result) <= sum_chars_rec(list1)
  ensures sum_chars_rec(result) <= sum_chars_rec(list2)
  ensures sum_chars_rec(list1) == sum_chars_rec(list2) ==> result == list1
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SumCharsRecProperty(list: seq<string>, i: nat)
  requires 0 <= i <= |list|
  ensures sum_chars_rec(list[i..]) == sum_chars_rec(list[i..])
{
  // Trivial lemma for clarity
}

lemma SumCharsRecSplit(list: seq<string>, i: nat)
  requires 0 <= i < |list|
  ensures sum_chars_rec(list[i..]) == |list[i]| + sum_chars_rec(list[i+1..])
{
  assert list[i..][0] == list[i];
  assert list[i..][1..] == list[i+1..];
}

lemma SumCharsRecAppend(list: seq<string>, i: nat, acc: nat)
  requires 0 <= i <= |list|
  ensures acc + sum_chars_rec(list[i..]) == acc + sum_chars_rec(list[i..])
{
  // Trivial lemma for clarity
}
// </vc-helpers>

// <vc-spec>
method SumChars(list: seq<string>) returns (sum: nat)
  // post-conditions-start
  ensures sum == sum_chars_rec(list)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var i := 0;
  
  while i < |list|
    invariant 0 <= i <= |list|
    invariant sum == sum_chars_rec(list[0..i])
  {
    // Before the update, we have: sum == sum_chars_rec(list[0..i])
    // We need to prove: sum + |list[i]| == sum_chars_rec(list[0..i+1])
    
    assert list[0..i+1] == list[0..i] + [list[i]];
    assert sum_chars_rec(list[0..i+1]) == sum_chars_rec(list[0..i] + [list[i]]);
    
    // Use the recursive definition
    calc {
      sum_chars_rec(list[0..i] + [list[i]]);
    == { assert list[0..i] + [list[i]] == list[0..i+1]; }
      sum_chars_rec(list[0..i+1]);
    == { 
      if i == 0 {
        assert list[0..1] == [list[0]];
        assert sum_chars_rec([list[0]]) == |list[0]| + sum_chars_rec([]);
        assert sum_chars_rec([]) == 0;
      } else {
        // Recursive expansion for general case
        assert |list[0..i+1]| > 0;
        assert list[0..i+1][0] == list[0];
        assert list[0..i+1][1..] == list[1..i+1];
      }
      SumCharsRecSplit(list, i);
      assert sum_chars_rec(list[i..i+1]) == |list[i]|;
    }
      sum_chars_rec(list[0..i]) + |list[i]|;
    }
    
    sum := sum + |list[i]|;
    i := i + 1;
  }
  
  assert i == |list|;
  assert list[0..|list|] == list;
}
// </vc-code>

