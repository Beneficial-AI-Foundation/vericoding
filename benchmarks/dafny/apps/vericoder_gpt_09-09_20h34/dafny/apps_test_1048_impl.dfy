function count_char(s: string, c: char): int
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + count_char(s[1..], c)
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

predicate ValidCommands(commands: string)
{
    forall i :: 0 <= i < |commands| ==> commands[i] in {'L', 'R', 'U', 'D'}
}

// <vc-helpers>
lemma CountCharNonNeg(s: string, c: char)
  ensures 0 <= count_char(s, c)
  decreases |s|
{
  if |s| == 0 {
  } else {
    CountCharNonNeg(s[1..], c);
    assert 0 <= (if s[0] == c then 1 else 0);
  }
}

lemma MinNonNeg(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures min(a, b) >= 0
{
  if a <= b {
  } else {
  }
}

lemma Min2LeSum(a: int, b: int)
  ensures 2 * min(a, b) <= a + b
{
  if a <= b {
    assert 2 * min(a, b) == 2 * a;
    assert 2 * a <= a + b;
  } else {
    assert 2 * min(a, b) == 2 * b;
    assert 2 * b <= a + b;
  }
}

lemma ValidCommandsTail(s: string)
  requires ValidCommands(s)
  requires |s| >= 1
  ensures ValidCommands(s[1..])
{
  assert |s[1..]| == |s| - 1;
  forall i | 0 <= i < |s[1..]|
    ensures s[1..][i] in {'L', 'R', 'U', 'D'}
  {
    var j := i + 1;
    assert 0 <= j < |s|;
    assert s[j] in {'L', 'R', 'U', 'D'};
    assert s[1..][i] == s[j];
  }
}

lemma SumCountsIsLength(s: string)
  requires ValidCommands(s)
  ensures count_char(s, 'L') + count_char(s, 'R') + count_char(s, 'U') + count_char(s, 'D') == |s|
  decreases |s|
{
  if |s| == 0 {
  } else {
    assert |s| >= 1;
    assert s[0] in {'L', 'R', 'U', 'D'};
    ValidCommandsTail(s);
    SumCountsIsLength(s[1..]);
    var ch := s[0];
    assert count_char(s, 'L') == (if ch == 'L' then 1 else 0) + count_char(s[1..], 'L');
    assert count_char(s, 'R') == (if ch == 'R' then 1 else 0) + count_char(s[1..], 'R');
    assert count_char(s, 'U') == (if ch == 'U' then 1 else 0) + count_char(s[1..], 'U');
    assert count_char(s, 'D') == (if ch == 'D' then 1 else 0) + count_char(s[1..], 'D');
    if ch == 'L' {
      assert ((1) + 0 + 0 + 0) == 1;
    } else if ch == 'R' {
      assert (0 + 1 + 0 + 0) == 1;
    } else if ch == 'U' {
      assert (0 + 0 + 1 + 0) == 1;
    } else {
      assert ch == 'D';
      assert (0 + 0 + 0 + 1) == 1;
    }
    assert |s[1..]| == |s| - 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, commands: string) returns (result: int)
    requires n >= 0
    requires |commands| == n
    requires ValidCommands(commands)
    ensures result >= 0
    ensures result <= n
    ensures result % 2 == 0
    ensures result == 2 * min(count_char(commands, 'L'), count_char(commands, 'R')) + 
                     2 * min(count_char(commands, 'U'), count_char(commands, 'D'))
// </vc-spec>
// <vc-code>
{
  result := 2 * min(count_char(commands, 'L'), count_char(commands, 'R')) +
            2 * min(count_char(commands, 'U'), count_char(commands, 'D'));

  var t := min(count_char(commands, 'L'), count_char(commands, 'R')) +
           min(count_char(commands, 'U'), count_char(commands, 'D'));
  assert result == 2 * t;
  assert result % 2 == 0;

  assert min(count_char(commands, 'L'), count_char(commands, 'R')) >= 0 by {
    CountCharNonNeg(commands, 'L');
    CountCharNonNeg(commands, 'R');
    MinNonNeg(count_char(commands, 'L'), count_char(commands, 'R'));
  }
  assert min(count_char(commands, 'U'), count_char(commands, 'D')) >= 0 by {
    CountCharNonNeg(commands, 'U');
    CountCharNonNeg(commands, 'D');
    MinNonNeg(count_char(commands, 'U'), count_char(commands, 'D'));
  }
  assert result >= 0;

  assert 2 * min(count_char(commands, 'L'), count_char(commands, 'R')) <= count_char(commands, 'L') + count_char(commands, 'R') by {
    Min2LeSum(count_char(commands, 'L'), count_char(commands, 'R'));
  }
  assert 2 * min(count_char(commands, 'U'), count_char(commands, 'D')) <= count_char(commands, 'U') + count_char(commands, 'D') by {
    Min2LeSum(count_char(commands, 'U'), count_char(commands, 'D'));
  }
  assert result <= (count_char(commands, 'L') + count_char(commands, 'R')) + (count_char(commands, 'U') + count_char(commands, 'D'));
  assert count_char(commands, 'L') + count_char(commands, 'R') + count_char(commands, 'U') + count_char(commands, 'D') == |commands| by {
    SumCountsIsLength(commands);
  }
  assert (count_char(commands, 'L') + count_char(commands, 'R')) + (count_char(commands, 'U') + count_char(commands, 'D')) ==
         count_char(commands, 'L') + count_char(commands, 'R') + count_char(commands, 'U') + count_char(commands, 'D');
}
// </vc-code>

