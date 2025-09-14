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
lemma count_char_decreases(s: string, c: char)
    decreases |s|
    ensures 0 <= count_char(s, c) <= |s|
{
    if |s| > 0 {
        count_char_decreases(s[1..], c);
        calc {
            count_char(s, c);
            (if s[0]==c then 1 else 0) + count_char(s[1..], c);
            { assert count_char(s[1..], c) >= 0; }
            (if s[0]==c then 1 else 0) + count_char(s[1..], c);
            >= { assert (if s[0]==c then 1 else 0) >= 0; } 0;
        }
        calc {
            count_char(s, c);
            (if s[0]==c then 1 else 0) + count_char(s[1..], c);
            <= { assert count_char(s[1..], c) <= |s[1..]|; assert (if s[0]==c then 1 else 0) <= 1; }
            1 + |s[1..]|;
            == |s|;
        }
    }
}

lemma total_count_lemma(commands: string)
    requires ValidCommands(commands)
    ensures count_char(commands, 'L') + count_char(commands, 'R') + 
            count_char(commands, 'U') + count_char(commands, 'D') == |commands|
{
    if |commands| == 0 {
    } else {
        total_count_lemma(commands[1..]);
        assert count_char(commands, 'L') == (if commands[0]=='L' then 1 else 0) + count_char(commands[1..], 'L');
        assert count_char(commands, 'R') == (if commands[0]=='R' then 1 else 0) + count_char(commands[1..], 'R');
        assert count_char(commands, 'U') == (if commands[0]=='U' then 1 else 0) + count_char(commands[1..], 'U');
        assert count_char(commands, 'D') == (if commands[0]=='D' then 1 else 0) + count_char(commands[1..], 'D');
        calc {
            count_char(commands, 'L') + count_char(commands, 'R') + count_char(commands, 'U') + count_char(commands, 'D');
            (if commands[0]=='L' then 1 else 0) + count_char(commands[1..], 'L') +
            (if commands[0]=='R' then 1 else 0) + count_char(commands[1..], 'R') +
            (if commands[0]=='U' then 1 else 0) + count_char(commands[1..], 'U') +
            (if commands[0]=='D' then 1 else 0) + count_char(commands[1..], 'D');
            == 
            (if commands[0]=='L' then 1 else 0) + (if commands[0]=='R' then 1 else 0) + 
            (if commands[0]=='U' then 1 else 0) + (if commands[0]=='D' then 1 else 0) +
            (count_char(commands[1..], 'L') + count_char(commands[1..], 'R') + count_char(commands[1..], 'U') + count_char(commands[1..], 'D'));
            {
                assert commands[0] in {'L','R','U','D'}; 
                assert (if commands[0]=='L' then 1 else 0) + (if commands[0]=='R' then 1 else 0) + 
                       (if commands[0]=='U' then 1 else 0) + (if commands[0]=='D' then 1 else 0) == 1;
            }
            1 + (count_char(commands[1..], 'L') + count_char(commands[1..], 'R') + count_char(commands[1..], 'U') + count_char(commands[1..], 'D'));
            { total_count_lemma(commands[1..]); }
            1 + |commands[1..]|;
            == 1 + (|commands| - 1);
            == |commands|;
        }
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
  var left_count := count_char(commands, 'L');
  var right_count := count_char(commands, 'R');
  var up_count := count_char(commands, 'U');
  var down_count := count_char(commands, 'D');
  count_char_decreases(commands, 'L');
  count_char_decreases(commands, 'R');
  count_char_decreases(commands, 'U');
  count_char_decreases(commands, 'D');
  total_count_lemma(commands);
  result := 2 * min(left_count, right_count) + 2 * min(up_count, down_count);
}
// </vc-code>

