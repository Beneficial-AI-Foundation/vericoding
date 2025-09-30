predicate ValidInput(n: int, s: string)
{
  1 <= n <= 200000 && |s| == n && 
  forall i :: 0 <= i < n ==> s[i] == 'D' || s[i] == 'R'
}

function CountD(s: string): int
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures CountD(s) >= 0
  ensures CountD(s) <= |s|
  ensures CountD(s) == 0 <==> forall i :: 0 <= i < |s| ==> s[i] != 'D'
{
  if |s| == 0 then 0
  else (if s[0] == 'D' then 1 else 0) + CountD(s[1..])
}

function CountR(s: string): int
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures CountR(s) >= 0
  ensures CountR(s) <= |s|
  ensures CountR(s) == 0 <==> forall i :: 0 <= i < |s| ==> s[i] != 'R'
{
  if |s| == 0 then 0
  else (if s[0] == 'R' then 1 else 0) + CountR(s[1..])
}

function OptimalEliminationGameWinner(s: string): string
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures OptimalEliminationGameWinner(s) == "D" || OptimalEliminationGameWinner(s) == "R"
  ensures CountD(s) == 0 ==> OptimalEliminationGameWinner(s) == "R"
  ensures CountR(s) == 0 ==> OptimalEliminationGameWinner(s) == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'D') ==> OptimalEliminationGameWinner(s) == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'R') ==> OptimalEliminationGameWinner(s) == "R"
  ensures OptimalEliminationGameWinner(s) == "D" ==> CountD(s) > 0
  ensures OptimalEliminationGameWinner(s) == "R" ==> CountR(s) > 0
{
  if CountD(s) == 0 then "R"
  else if CountR(s) == 0 then "D"
  else if CountD(s) >= CountR(s) then "D"
  else "R"
}

// <vc-helpers>
lemma CountDCorrect(s: string)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures CountD(s) + CountR(s) == |s|
{
  if |s| == 0 {
  } else {
    CountDCorrect(s[1..]);
  }
}

lemma CountDSubstring(s: string, start: int, end: int)
  requires 0 <= start <= end <= |s|
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures CountD(s[start..end]) >= 0
  ensures CountD(s[start..end]) <= end - start
{
}

lemma CountRSubstring(s: string, start: int, end: int)
  requires 0 <= start <= end <= |s|
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures CountR(s[start..end]) >= 0
  ensures CountR(s[start..end]) <= end - start
{
}

lemma CountDExtend(s: string, i: int)
  requires 0 <= i < |s|
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  ensures CountD(s[0..i+1]) == CountD(s[0..i]) + (if s[i] == 'D' then 1 else 0)
{
  if i == 0 {
    assert s[0..1] == [s[0]];
    assert CountD(s[0..1]) == (if s[0] == 'D' then 1 else 0);
    assert s[0..0] == [];
    assert CountD(s[0..0]) == 0;
  } else {
    assert s[0..i+1] == s[0..i] + [s[i]];
    var prefix := s[0..i];
    var extended := s[0..i+1];
    assert extended == prefix + [s[i]];
    CountDAppend(prefix, [s[i]]);
  }
}

lemma CountRExtend(s: string, i: int)
  requires 0 <= i < |s|
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  ensures CountR(s[0..i+1]) == CountR(s[0..i]) + (if s[i] == 'R' then 1 else 0)
{
  if i == 0 {
    assert s[0..1] == [s[0]];
    assert CountR(s[0..1]) == (if s[0] == 'R' then 1 else 0);
    assert s[0..0] == [];
    assert CountR(s[0..0]) == 0;
  } else {
    assert s[0..i+1] == s[0..i] + [s[i]];
    var prefix := s[0..i];
    var extended := s[0..i+1];
    assert extended == prefix + [s[i]];
    CountRAppend(prefix, [s[i]]);
  }
}

lemma CountDAppend(s1: string, s2: string)
  requires forall i :: 0 <= i < |s1| ==> s1[i] == 'D' || s1[i] == 'R'
  requires forall i :: 0 <= i < |s2| ==> s2[i] == 'D' || s2[i] == 'R'
  ensures CountD(s1 + s2) == CountD(s1) + CountD(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert (s1 + s2)[0] == s1[0];
    assert (s1 + s2)[1..] == s1[1..] + s2;
    CountDAppend(s1[1..], s2);
  }
}

lemma CountRAppend(s1: string, s2: string)
  requires forall i :: 0 <= i < |s1| ==> s1[i] == 'D' || s1[i] == 'R'
  requires forall i :: 0 <= i < |s2| ==> s2[i] == 'D' || s2[i] == 'R'
  ensures CountR(s1 + s2) == CountR(s1) + CountR(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert (s1 + s2)[0] == s1[0];
    assert (s1 + s2)[1..] == s1[1..] + s2;
    CountRAppend(s1[1..], s2);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
  requires ValidInput(n, s)
  ensures result == "D" || result == "R"
  ensures result == "D" ==> CountD(s) > 0
  ensures result == "R" ==> CountR(s) > 0
  ensures CountD(s) == 0 ==> result == "R"
  ensures CountR(s) == 0 ==> result == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'D') ==> result == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'R') ==> result == "R"
  ensures result == OptimalEliminationGameWinner(s)
// </vc-spec>
// <vc-code>
{
  var countD := 0;
  var countR := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant countD >= 0
    invariant countR >= 0
    invariant countD == CountD(s[0..i])
    invariant countR == CountR(s[0..i])
    invariant countD + countR == i
  {
    CountDExtend(s, i);
    CountRExtend(s, i);
    
    if s[i] == 'D' {
      countD := countD + 1;
    } else {
      countR := countR + 1;
    }
    i := i + 1;
  }
  
  assert s[0..n] == s;
  assert countD == CountD(s);
  assert countR == CountR(s);
  
  if countD == 0 {
    result := "R";
  } else if countR == 0 {
    result := "D";
  } else if countD >= countR {
    result := "D";
  } else {
    result := "R";
  }
}
// </vc-code>

