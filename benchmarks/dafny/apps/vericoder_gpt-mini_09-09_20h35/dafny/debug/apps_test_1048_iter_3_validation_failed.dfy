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
lemma CountCharBounds(s: string, c: char)
    ensures 0 <= count_char(s, c) <= |s|
    decreases |s|
{
    if |s| == 0 {
        assert count_char(s, c) == 0;
    } else {
        var rest := s[1..];
        CountCharBounds(rest, c);
        assert 0 <= count_char(rest, c);
        assert count_char(rest, c) <= |rest|;
        if s[0] == c {
            assert count_char(s, c) == 1 + count_char(rest, c);
            assert 0 <= 1 + count_char(rest, c);
            assert 1 + count_char(rest, c) <= 1 + |rest|;
            assert 1 + |rest| == |s|;
        } else {
            assert count_char(s, c) == count_char(rest, c);
            assert 0 <= count_char(rest, c);
            assert count_char(rest, c) <= |rest|;
            assert |rest| == |s| - 1;
        }
    }
}

lemma ValidCommandsTail(s: string)
    requires ValidCommands(s)
    ensures ValidCommands(s[1..])
    decreases |s|
{
    if |s| == 0 {
        // vacuously true
    } else {
        var rest := s[1..];
        assert (forall i :: 0 <= i < |rest| ==> rest[i] in {'L','R','U','D'})
        {
            fix i;
            assume 0 <= i < |rest|;
            assert 0 <= 1 + i < |s|;
            // instantiate the hypothesis ValidCommands(s) for index 1 + i
            assert s[1 + i] in {'L','R','U','D'};
            assert rest[i] == s[1 + i];
            assert rest[i] in {'L','R','U','D'};
        }
    }
}

lemma CountCharSum(s: string)
    requires ValidCommands(s)
    ensures count_char(s, 'L') + count_char(s, 'R') + count_char(s, 'U') + count_char(s, 'D') == |s|
    decreases |s|
{
    if |s| == 0 {
        assert count_char(s, 'L') == 0;
        assert count_char(s, 'R') == 0;
        assert count_char(s, 'U') == 0;
        assert count_char(s, 'D') == 0;
    } else {
        var rest := s[1..];
        ValidCommandsTail(s);
        CountCharSum(rest);
        if s[0] == 'L' {
            assert count_char(s, 'L') == 1 + count_char(rest, 'L');
            assert count_char(s, 'R') == count_char(rest, 'R');
            assert count_char(s, 'U') == count_char(rest, 'U');
            assert count_char(s, 'D') == count_char(rest, 'D');
        } else if s[0] == 'R' {
            assert count_char(s, 'L') == count_char(rest, 'L');
            assert count_char(s, 'R') == 1 + count_char(rest, 'R');
            assert count_char(s, 'U') == count_char(rest, 'U');
            assert count_char(s, 'D') == count_char(rest, 'D');
        } else if s[0] == 'U' {
            assert count_char(s, 'L') == count_char(rest, 'L');
            assert count_char(s, 'R') == count_char(rest, 'R');
            assert count_char(s, 'U') == 1 + count_char(rest, 'U');
            assert count_char(s, 'D') == count_char(rest, 'D');
        } else {
            // s[0] == 'D'
            assert count_char(s, 'L') == count_char(rest, 'L');
            assert count_char(s, 'R') == count_char(rest, 'R');
            assert count_char(s, 'U') == count_char(rest, 'U');
            assert count_char(s, 'D') == 1 + count_char(rest, 'D');
        }
        assert count_char(s, 'L') + count_char(s, 'R') + count_char(s, 'U') + count_char(s, 'D')
               == (count_char(rest, 'L') + count_char(rest, 'R') + count_char(rest, 'U') + count_char(rest, 'D')) + 1;
        assert (count_char(rest, 'L') + count_char(rest, 'R') + count_char(rest, 'U') + count_char(rest, 'D')) == |rest|;
        assert |rest| + 1 == |s|;
    }
}

lemma TwiceMinLeSum(a: int, b: int)
    ensures 2 * min(a, b) <= a + b
{
    if a <= b {
        assert min(a, b) == a;
        assert 2 * a <= a + b;
    } else {
        assert min(a, b) == b;
        assert 2 * b <= a + b;
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
  var l := count_char(commands, 'L');
  var r := count_char(commands, 'R');
  var u := count_char(commands, 'U');
  var d := count_char(commands, 'D');

  CountCharBounds(commands, 'L');
  CountCharBounds(commands, 'R');
  CountCharBounds(commands, 'U');
  CountCharBounds(commands, 'D');

  CountCharSum(commands);

  TwiceMinLeSum(l, r);
  TwiceMinLeSum(u, d);

  result := 2 * min(l, r) + 2 * min(u, d);
}
// </vc-code>

