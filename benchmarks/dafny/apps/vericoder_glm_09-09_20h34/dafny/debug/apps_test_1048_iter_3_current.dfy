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
lemma count_char_prefix(s: string, c: char, i: int)
    requires 0 <= i <= |s|
    ensures count_char(s, c) == count_char(s[0..i], c) + count_char(s[i..], c)
{
    if i == 0 {
        calc {
            count_char(s, c);
            count_char(s[0..0] + s[0..], c);
            { assert s[0..0] == ""; }
            count_char("", c) + count_char(s[0..], c);
            { assert count_char("", c) == 0; }
            count_char(s[0..], c);
        }
    } else if i == |s| {
        calc {
            count_char(s, c);
            count_char(s[0..|s|] + s[|s|..], c);
            { assert s[|s|..] == ""; }
            count_char(s[0..|s|], c) + count_char("", c);
            { assert count_char("", c) == 0; }
            count_char(s[0..|s|], c);
        }
    } else {
        calc {
            count_char(s, c);
            { assert s == s[0..i] + s[i..]; }
            count_char(s[0..i] + s[i..], c);
            count_char(s[0..i], c) + count_char(s[i..], c);
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
  var L := 0;
  var R := 0;
  var U := 0;
  var D := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant L == count_char(commands[0..i], 'L')
    invariant R == count_char(commands[0..i], 'R')
    invariant U == count_char(commands[0..i], 'U')
    invariant D == count_char(commands[0..i], 'D')
  {
    if commands[i] == 'L' {
      L := L + 1;
    } else if commands[i] == 'R' {
      R := R + 1;
    } else if commands[i] == 'U' {
      U := U + 1;
    } else {
      D := D + 1;
    }
    i := i + 1;
  }
  calc {
      2 * min(count_char(commands, 'L'), count_char(commands, 'R')) + 2 * min(count_char(commands, 'U'), count_char(commands, 'D'));
      == 
      2 * min( count_char(commands[0..n], 'L') + count_char(commands[n..], 'L'), 
               count_char(commands[0..n], 'R') + count_char(commands[n..], 'R') ) 
      + 2 * min( count_char(commands[0..n], 'U') + count_char(commands[n..], 'U'), 
                 count_char(commands[0..n], 'D') + count_char(commands[n..], 'D') )
      { 
        count_char_prefix(commands, 'L', n);
        count_char_prefix(commands, 'R', n);
        count_char_prefix(commands, 'U', n);
        count_char_prefix(commands, 'D', n);
      }
      == 
      2 * min( count_char(commands[0..n], 'L'), count_char(commands[0..n], 'R') ) 
      + 2 * min( count_char(commands[0..n], 'U'), count_char(commands
// </vc-code>

