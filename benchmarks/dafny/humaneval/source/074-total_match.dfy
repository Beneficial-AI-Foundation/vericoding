method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| == |list1| || |result| == |list2|
  ensures result == list1 || result == list2
  ensures sum_chars_rec(result) <= sum_chars_rec(list1)
  ensures sum_chars_rec(result) <= sum_chars_rec(list2)
  ensures sum_chars_rec(list1) == sum_chars_rec(list2) ==> result == list1
  // post-conditions-end
{
  // impl-start
  var sum1 := SumChars(list1);
  var sum2 := SumChars(list2);

  if sum1 <= sum2 {
    return list1;
  } else {
    return list2;
  }
  // impl-end
}

function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}
// pure-end
lemma sum_prop(s: seq<string>)
    requires |s| > 0
    ensures sum_chars_rec(s) == sum_chars_rec(s[..|s| - 1]) + |s[ |s| - 1 ]|
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}
// pure-end
method SumChars(list: seq<string>) returns (sum: nat)
  // post-conditions-start
  ensures sum == sum_chars_rec(list)
  // post-conditions-end
{
  // impl-start
    sum := 0;
    var i := 0;
    while (i < |list|)
        // invariants-start
        invariant 0 <= i <= |list|
        invariant sum == sum_chars_rec(list[..i])
        // invariants-end
    {
        sum := sum + |list[i]|;
        // assert-start
        assert sum_chars_rec(list[..i + 1]) == sum_chars_rec(list[..i]) + |list[i]| by {
            assert list[..i+1][..i] == list[..i];
            sum_prop(list[..i + 1]);
        }
        // assert-end

        i := i + 1;
    }
    assert list == list[..|list|]; // assert-line
  // impl-end
}
