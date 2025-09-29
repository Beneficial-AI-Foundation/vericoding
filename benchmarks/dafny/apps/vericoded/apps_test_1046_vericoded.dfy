function CountOccurrences(s: seq<int>, x: int): int
  ensures CountOccurrences(s, x) >= 0
{
  if |s| == 0 then 0
  else (if s[0] == x then 1 else 0) + CountOccurrences(s[1..], x)
}

function CountPairs(s: seq<int>): int
  ensures CountPairs(s) >= 0
{
  var positive_sessions := FilterPositive(s);
  CountPairsHelper(positive_sessions)
}

function FilterPositive(s: seq<int>): seq<int>
  ensures forall i :: 0 <= i < |FilterPositive(s)| ==> FilterPositive(s)[i] > 0
{
  if |s| == 0 then []
  else if s[0] > 0 then [s[0]] + FilterPositive(s[1..])
  else FilterPositive(s[1..])
}

function CountPairsHelper(s: seq<int>): int
  decreases |s|
  ensures CountPairsHelper(s) >= 0
{
  if |s| <= 1 then 0
  else 
    var count := CountOccurrences(s, s[0]);
    var remaining := RemoveAllOccurrences(s, s[0]);
    (if count == 2 then 1 else 0) + CountPairsHelper(remaining)
}

function RemoveAllOccurrences(s: seq<int>, x: int): seq<int>
  ensures |RemoveAllOccurrences(s, x)| <= |s|
{
  if |s| == 0 then []
  else if s[0] == x then RemoveAllOccurrences(s[1..], x)
  else [s[0]] + RemoveAllOccurrences(s[1..], x)
}

predicate ExistsIndex(s: seq<int>, x: int)
{
  exists i :: 0 <= i < |s| && s[i] == x
}

// <vc-helpers>
lemma CountOccurrencesNonNegative(s: seq<int>, x: int)
  ensures CountOccurrences(s, x) >= 0
{
}

lemma CountOccurrencesEmpty(x: int)
  ensures CountOccurrences([], x) == 0
{
}

lemma CountOccurrencesProperties(s: seq<int>, x: int)
  ensures CountOccurrences(s, x) >= 0
  ensures CountOccurrences(s, x) <= |s|
{
  if |s| == 0 {
  } else {
    CountOccurrencesProperties(s[1..], x);
  }
}

lemma FilterPositivePreservesElements(s: seq<int>)
  ensures forall i :: 0 <= i < |FilterPositive(s)| ==> exists j :: 0 <= j < |s| && s[j] == FilterPositive(s)[i]
{
  if |s| == 0 {
  } else if s[0] > 0 {
    FilterPositivePreservesElements(s[1..]);
    var filtered_rest := FilterPositive(s[1..]);
    forall i | 1 <= i < |FilterPositive(s)|
      ensures exists j :: 0 <= j < |s| && s[j] == FilterPositive(s)[i]
    {
      assert FilterPositive(s)[i] == filtered_rest[i-1];
      var j_rest :| 0 <= j_rest < |s[1..]| && s[1..][j_rest] == filtered_rest[i-1];
      assert s[j_rest + 1] == FilterPositive(s)[i];
    }
  } else {
    FilterPositivePreservesElements(s[1..]);
  }
}

lemma RemoveAllOccurrencesCorrect(s: seq<int>, x: int)
  ensures CountOccurrences(RemoveAllOccurrences(s, x), x) == 0
  ensures forall y :: y != x ==> CountOccurrences(RemoveAllOccurrences(s, x), y) == CountOccurrences(s, y)
{
  if |s| == 0 {
  } else {
    RemoveAllOccurrencesCorrect(s[1..], x);
  }
}

lemma RemoveAllOccurrencesPreservesPositivity(s: seq<int>, x: int)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures forall i :: 0 <= i < |RemoveAllOccurrences(s, x)| ==> RemoveAllOccurrences(s, x)[i] > 0
{
  if |s| == 0 {
  } else if s[0] == x {
    RemoveAllOccurrencesPreservesPositivity(s[1..], x);
  } else {
    RemoveAllOccurrencesPreservesPositivity(s[1..], x);
  }
}

lemma CountPairsCorrectness(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures CountPairsHelper(s) >= 0
  decreases |s|
{
  if |s| <= 1 {
  } else {
    var count := CountOccurrences(s, s[0]);
    var remaining := RemoveAllOccurrences(s, s[0]);
    RemoveAllOccurrencesCorrect(s, s[0]);
    RemoveAllOccurrencesPreservesPositivity(s, s[0]);
    CountPairsCorrectness(remaining);
  }
}

lemma CountOccurrencesSlice(s: seq<int>, x: int, j: int)
  requires 0 <= j <= |s|
  ensures CountOccurrences(s[0..j], x) + CountOccurrences(s[j..], x) == CountOccurrences(s, x)
{
  if j == 0 {
    assert s[0..j] == [];
    assert s[j..] == s;
  } else if j == |s| {
    assert s[j..] == [];
    assert s[0..j] == s;
  } else {
    assert s == s[0..j] + s[j..];
    CountOccurrencesConcat(s[0..j], s[j..], x);
  }
}

lemma CountOccurrencesConcat(s1: seq<int>, s2: seq<int>, x: int)
  ensures CountOccurrences(s1 + s2, x) == CountOccurrences(s1, x) + CountOccurrences(s2, x)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    CountOccurrencesConcat(s1[1..], s2, x);
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
  }
}

lemma AllPositiveCountAtMost2(sessions: seq<int>)
  requires forall id :: id > 0 ==> CountOccurrences(sessions, id) <= 2
  ensures forall i :: 0 <= i < |sessions| && sessions[i] > 0 ==> CountOccurrences(sessions, sessions[i]) <= 2
{
}

lemma CountOccurrencesIncrementStep(s: seq<int>, x: int, j: int)
  requires 0 <= j < |s|
  ensures CountOccurrences(s[0..j+1], x) == CountOccurrences(s[0..j], x) + (if s[j] == x then 1 else 0)
{
  assert s[0..j+1] == s[0..j] + [s[j]];
  CountOccurrencesConcat(s[0..j], [s[j]], x);
}

lemma CountOccurrencesNotInSequence(s: seq<int>, x: int)
  requires forall i :: 0 <= i < |s| ==> s[i] != x
  ensures CountOccurrences(s, x) == 0
{
  if |s| == 0 {
  } else {
    CountOccurrencesNotInSequence(s[1..], x);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, sessions: seq<int>) returns (result: int)
  requires n >= 1
  requires |sessions| == n
  requires forall i :: 0 <= i < |sessions| ==> sessions[i] >= 0
  ensures result == -1 || result >= 0
  ensures result == -1 ==> exists id :: id > 0 && CountOccurrences(sessions, id) > 2
  ensures result >= 0 ==> forall id :: id > 0 ==> CountOccurrences(sessions, id) <= 2
  ensures result >= 0 ==> result == CountPairs(sessions)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> sessions[j] >= 0
    invariant forall id :: id > 0 && (exists k :: 0 <= k < i && sessions[k] == id) ==> CountOccurrences(sessions, id) <= 2
  {
    if sessions[i] > 0 {
      var count := 0;
      var j := 0;
      while j < n
        invariant 0 <= j <= n
        invariant count == CountOccurrences(sessions[0..j], sessions[i])
        invariant count >= 0
      {
        if sessions[j] == sessions[i] {
          count := count + 1;
        }
        CountOccurrencesIncrementStep(sessions, sessions[i], j);
        j := j + 1;
      }
      
      CountOccurrencesSlice(sessions, sessions[i], n);
      assert count == CountOccurrences(sessions, sessions[i]);
      
      if count > 2 {
        return -1;
      }
    }
    i := i + 1;
  }
  
  assert forall id :: id > 0 && (exists k :: 0 <= k < n && sessions[k] == id) ==> CountOccurrences(sessions, id) <= 2;
  
  forall id | id > 0
    ensures CountOccurrences(sessions, id) <= 2
  {
    if exists k :: 0 <= k < n && sessions[k] == id {
      assert CountOccurrences(sessions, id) <= 2;
    } else {
      CountOccurrencesNotInSequence(sessions, id);
      assert CountOccurrences(sessions, id) == 0;
    }
  }
  
  FilterPositivePreservesElements(sessions);
  AllPositiveCountAtMost2(sessions);
  result := CountPairs(sessions);
}
// </vc-code>

