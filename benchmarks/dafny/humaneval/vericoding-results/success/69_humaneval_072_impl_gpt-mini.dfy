// <vc-preamble>

predicate is_palindrome(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] == s[|s| - 1 - i]
}

function sum_elements(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum_elements(s[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prove sum distributes over concatenation by induction */
lemma SumConcat(s1: seq<int>, s2: seq<int>)
  ensures sum_elements(s1 + s2) == sum_elements(s1) + sum_elements(s2)
  decreases |s1|
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
    assert sum_elements(s1 + s2) == sum_elements(s2);
    assert sum_elements(s1) == 0;
  } else {
    var x := s1[0];
    SumConcat(s1[1..], s2);
    assert (s1 + s2)[0] == x;
    assert (s1 + s2)[1..] == (s1[1..]) + s2;
    assert sum_elements(s1 + s2) == (s1 + s2)[0] + sum_elements((s1 + s2)[1..]);
    assert (s1 + s2)[0] + sum_elements((s1 + s2)[1..]) == x + sum_elements((s1[1..]) + s2);
    assert sum_elements(s1) == x + sum_elements(s1[1..]);
    assert sum_elements((s1[1..]) + s2) == sum_elements(s1[1..]) + sum_elements(s2);
    assert x + sum_elements((s1[1..]) + s2) == x + (sum_elements(s1[1..]) + sum_elements(s2));
    assert x + (sum_elements(s1[1..]) + sum_elements(s2)) == (x + sum_elements(s1[1..])) + sum_elements(s2);
    assert (x + sum_elements(s1[1..])) + sum_elements(s2) == sum_elements(s1) + sum_elements(s2);
  }
}

// </vc-helpers>

// <vc-spec>
method will_it_fly(q: seq<int>, w: int) returns (result: bool)
    ensures result == (is_palindrome(q) && sum_elements(q) <= w)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute palindrome and sum comparison */
  result := is_palindrome(q) && sum_elements(q) <= w;
}

// </vc-code>
