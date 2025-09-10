predicate ValidInput(n: int, s: string)
{
    n >= 1 && n <= 2000 && |s| == n && 
    forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(result: string, n: int)
{
    |result| == n && 
    forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z'
}

predicate PreservesCharacters(s: string, result: string)
{
    multiset(s) == multiset(result)
}

// <vc-helpers>
lemma CountLemma(s: string, result: string)
  requires |s| == |result|
  requires multiset(s) == multiset(result)
  ensures forall c :: 'a' <= c <= 'z' ==> count(s, c) == count(result, c)
{
}

function count(s: string, c: char): nat
  decreases s
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + count(s[1..], c)
}

lemma PermutationLemma(s1: string, s2: string)
  requires multiset(s1) == multiset(s2)
  ensures |s1| == |s2|
{
}

lemma MultisetPreservationLemma(s: string, result: string)
  requires multiset(s) == multiset(result)
  requires ValidInput(|s|, s)
  ensures ValidOutput(result, |s|) && PreservesCharacters(s, result)
  ensures forall c :: 'a' <= c <= 'z' ==> count(s, c) == count(result, c)
{
  PermutationLemma(s, result);
  
  assert ValidOutput(result, |s|) {
    assert |result| == |s|;
    var c: char :| 'a' <= c <= 'z';
    assert forall i :: 0 <= i < |result| ==> 'a' <= result[i] <= 'z' by {
      assert multiset(s) == multiset(result);
      assert forall x :: x in multiset(s) ==> 'a' <= x <= 'z';
    }
  }
  
  CountLemma(s, result);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
    requires ValidInput(n, s)
    ensures ValidOutput(result, n)
    ensures PreservesCharacters(s, result)
// </vc-spec>
// <vc-code>
{
  result := s;
  MultisetPreservationLemma(s, result);
}
// </vc-code>

