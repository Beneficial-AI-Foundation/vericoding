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
lemma CountDRSum(s: string)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures CountD(s) + CountR(s) == |s|
{
  if |s| == 0 {
  } else {
    CountDRSum(s[1..]);
  }
}

lemma CountDPrefix(s: string, i: int)
  requires 0 <= i <= |s|
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  ensures CountD(s[..i]) == CountD(s[..i-1]) + (if i > 0 && s[i-1] == 'D' then 1 else 0)
{
  if i == 0 {
    assert s[..0] == "";
  } else {
    assert s[..i] == s[..i-1] + [s[i-1]];
    CountDAppend(s[..i-1], [s[i-1]]);
  }
}

lemma CountRPrefix(s: string, i: int)
  requires 0 <= i <= |s|
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  ensures CountR(s[..i]) == CountR(s[..i-1]) + (if i > 0 && s[i-1] == 'R' then 1 else 0)
{
  if i == 0 {
    assert s[..0] == "";
  } else {
    assert s[..i] == s[..i-1] + [s[i-1]];
    CountRAppend(s[..i-1], [s[i-1]]);
  }
}

lemma CountDAppend(s1: string, s2: string)
  requires forall i :: 0 <= i < |s1| ==> s1[i] == 'D' || s1[i] == 'R'
  requires forall i :: 0 <= i < |s2| ==> s2[i] == 'D' || s2[i] == 'R'
  ensures CountD(s1 + s2) == CountD(s1) + CountD(s2)
{
  if |s2| == 0 {
    assert s1 + s2 == s1;
  } else {
    CountDAppend(s1, s2[..|s2|-1]);
  }
}

lemma CountRAppend(s1: string, s2: string)
  requires forall i :: 0 <= i < |s1| ==> s1[i] == 'D' || s1[i] == 'R'
  requires forall i :: 0 <= i < |s2| ==> s2[i] == 'D' || s2[i] == 'R'
  ensures CountR(s1 + s2) == CountR(s1) + CountR(s2)
{
  if |s2| == 0 {
    assert s1 + s2 == s1;
  } else {
    CountRAppend(s1, s2[..|s2|-1]);
  }
}

method CountDIterative(s: string) returns (count: int)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures count == CountD(s)
{
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == CountD(s[..i])
  {
    CountDPrefix(s, i+1);
    if s[i] == 'D' {
      count := count + 1;
    }
    i := i + 1;
  }
}

method CountRIterative(s: string) returns (count: int)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures count == CountR(s)
{
  count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == CountR(s[..i])
  {
    CountRPrefix(s, i+1);
    if s[i] == 'R' {
      count := count + 1;
    }
    i := i + 1;
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
    invariant countD == CountD(s[..i])
    invariant countR == CountR(s[..i])
  {
    CountDPrefix(s, i+1);
    CountRPrefix(s, i+1);
    if s[i] == 'D' {
      countD := countD + 1;
    } else {
      countR := countR + 1;
    }
    i := i + 1;
  }
  
  assert s[..n] == s;
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

