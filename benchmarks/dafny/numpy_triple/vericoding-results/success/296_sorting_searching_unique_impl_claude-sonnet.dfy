// <vc-preamble>
// Method to find unique elements in an array, removing duplicates and sorting
// </vc-preamble>

// <vc-helpers>
predicate is_sorted(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

function remove_duplicates(s: seq<real>): seq<real>
  ensures forall x :: x in remove_duplicates(s) ==> x in s
  ensures forall x :: x in s ==> x in remove_duplicates(s)
  ensures forall i, j :: 0 <= i < j < |remove_duplicates(s)| ==> remove_duplicates(s)[i] != remove_duplicates(s)[j]
{
  if |s| == 0 then []
  else if s[0] in s[1..] then remove_duplicates(s[1..])
  else [s[0]] + remove_duplicates(s[1..])
}

function insert_sorted(x: real, s: seq<real>): seq<real>
  requires is_sorted(s)
  ensures is_sorted(insert_sorted(x, s))
  ensures x in insert_sorted(x, s)
  ensures forall y :: y in s ==> y in insert_sorted(x, s)
  ensures forall y :: y in insert_sorted(x, s) ==> y == x || y in s
  ensures |insert_sorted(x, s)| <= |s| + 1
  decreases |s|
{
  if |s| == 0 then [x]
  else if x < s[0] then [x] + s
  else if x == s[0] then s
  else 
    var recursive_result := insert_sorted(x, s[1..]);
    var result := [s[0]] + recursive_result;
    assert is_sorted(recursive_result);
    assert forall k :: 1 <= k < |recursive_result| ==> x < recursive_result[k] || x == recursive_result[k-1] || recursive_result[k-1] < recursive_result[k];
    result
}

function sort_and_dedupe(s: seq<real>): seq<real>
  ensures is_sorted(sort_and_dedupe(s))
  ensures forall x :: x in sort_and_dedupe(s) ==> x in s
  ensures forall x :: x in s ==> x in sort_and_dedupe(s)
  ensures forall i, j :: 0 <= i < j < |sort_and_dedupe(s)| ==> sort_and_dedupe(s)[i] != sort_and_dedupe(s)[j]
  ensures |sort_and_dedupe(s)| <= |s|
  decreases |s|
{
  if |s| == 0 then []
  else insert_sorted(s[0], sort_and_dedupe(s[1..]))
}

/* helper modified by LLM (iteration 5): simplified insert_sorted assertions to fix verification */
// </vc-helpers>

// <vc-spec>
method unique(ar: seq<real>) returns (result: seq<real>)
  // No preconditions - works on any input array
  ensures |result| <= |ar|
  // The result is sorted in ascending order
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
  // No duplicates in the result (defines uniqueness)
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
  // Every element in result comes from the input array
  ensures forall i :: 0 <= i < |result| ==> result[i] in ar
  // Every distinct element from input appears exactly once in result  
  ensures forall x :: x in ar ==> x in result
  ensures forall x :: x in result ==> x in ar
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): using sort_and_dedupe function */
  result := sort_and_dedupe(ar);
}
// </vc-code>
