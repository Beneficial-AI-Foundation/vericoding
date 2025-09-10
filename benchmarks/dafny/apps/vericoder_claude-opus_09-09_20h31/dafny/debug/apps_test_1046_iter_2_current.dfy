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
lemma FilterPositiveSubset(s: seq<int>)
  ensures forall x :: x in FilterPositive(s) ==> x in s
{
  if |s| == 0 {
  } else if s[0] > 0 {
    FilterPositiveSubset(s[1..]);
  } else {
    FilterPositiveSubset(s[1..]);
  }
}

lemma CountOccurrencesFilterPositive(s: seq<int>, x: int)
  requires x > 0
  ensures CountOccurrences(FilterPositive(s), x) == CountOccurrences(s, x)
{
  if |s| == 0 {
  } else if s[0] > 0 {
    if s[0] == x {
      CountOccurrencesFilterPositive(s[1..], x);
    } else {
      CountOccurrencesFilterPositive(s[1..], x);
    }
  } else {
    CountOccurrencesFilterPositive(s[1..], x);
  }
}

lemma RemoveAllOccurrencesProperties(s: seq<int>, x: int)
  ensures forall y :: y != x && y in s ==> y in RemoveAllOccurrences(s, x)
  ensures forall y :: y in RemoveAllOccurrences(s, x) ==> y in s && y != x
  ensures CountOccurrences(RemoveAllOccurrences(s, x), x) == 0
{
  if |s| == 0 {
  } else if s[0] == x {
    RemoveAllOccurrencesProperties(s[1..], x);
  } else {
    RemoveAllOccurrencesProperties(s[1..], x);
  }
}

lemma CountOccurrencesSlice(s: seq<int>, x: int, j: int)
  requires 0 <= j <= |s|
  ensures CountOccurrences(s[..j], x) + CountOccurrences(s[j..], x) == CountOccurrences(s, x)
{
  if j == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
  } else if j == |s| {
    assert s[..|s|] == s;
    assert s[|s|..] == [];
  } else {
    if j == 1 {
      assert s[..1] == [s[0]];
    }
    CountOccurrencesSlice(s[1..], x, j-1);
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
  var positive_sessions := [];
  
  // Filter positive sessions
  while i < |sessions|
    invariant 0 <= i <= |sessions|
    invariant positive_sessions == FilterPositive(sessions[..i])
  {
    if sessions[i] > 0 {
      positive_sessions := positive_sessions + [sessions[i]];
    }
    i := i + 1;
  }
  
  assert sessions[..i] == sessions;
  assert positive_sessions == FilterPositive(sessions);
  
  // Check if any positive ID appears more than twice
  i := 0;
  while i < |positive_sessions|
    invariant 0 <= i <= |positive_sessions|
    invariant forall j :: 0 <= j < i ==> CountOccurrences(positive_sessions, positive_sessions[j]) <= 2
    invariant forall id :: id in positive_sessions[..i] ==> CountOccurrences(positive_sessions, id) <= 2
  {
    var count := 0;
    var j := 0;
    
    // Count occurrences of positive_sessions[i]
    while j < |positive_sessions|
      invariant 0 <= j <= |positive_sessions|
      invariant count == CountOccurrences(positive_sessions[..j], positive_sessions[i])
    {
      if positive_sessions[j] == positive_sessions[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    
    assert positive_sessions[..j] == positive_sessions;
    assert count == CountOccurrences(positive_sessions, positive_sessions[i]);
    
    if count > 2 {
      CountOccurrencesFilterPositive(sessions, positive_sessions[i]);
      assert CountOccurrences(sessions, positive_sessions[i]) > 2;
      return -1;
    }
    
    i := i + 1;
  }
  
  assert forall id :: id in positive_sessions ==> CountOccurrences(positive_sessions, id) <= 2;
  FilterPositiveSubset(sessions);
  assert forall id :: id > 0 && id in sessions ==> (id in FilterPositive(sessions) || id !in FilterPositive(sessions));
  
  // Prove that all positive IDs have count <= 2
  forall id | id > 0
    ensures CountOccurrences(sessions, id) <= 2
  {
    CountOccurrencesFilterPositive(sessions, id);
    if id in positive_sessions {
      assert CountOccurrences(positive_sessions, id) <= 2;
    } else {
      assert CountOccurrences(positive_sessions, id) == 0;
    }
  }
  
  // Count pairs
  result := CountPairsHelper(positive_sessions);
  assert result == CountPairs(sessions);
}
// </vc-code>

