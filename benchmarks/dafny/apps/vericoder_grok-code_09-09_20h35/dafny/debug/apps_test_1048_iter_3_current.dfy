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
lemma CountCharNonnegative(s: string, c: char)
  ensures count_char(s, c) >= 0
{
  if |s| > 0 {
    CountCharNonnegative(s[1..], c);
  }
}

lemma MinSmaller(a: int, b: int)
  ensures min(a, b) <= a && min(a, b) <= b
{
  if a <= b {
  } else {
  }
}

lemma ExprLeqN(commands: string)
  requires |commands| >= 0
  requires ValidCommands(commands)
  ensures 2 * min(count_char(commands, 'L'), count_char(commands, 'R')) + 
          2 * min(count_char(commands, 'U'), count_char(commands, 'D')) <= |commands|
{
  CountCharNonnegative(commands, 'L');
  CountCharNonnegative(commands, 'R');
  CountCharNonnegative(commands, 'U');
  CountCharNonnegative(commands, 'D');
  MinSmaller(count_char(commands, 'L'), count_char(commands, 'R'));
  MinSmaller(count_char(commands, 'U'), count_char(commands, 'D'));
  var L := count_char(commands, 'L');
  var R := count_char(commands, 'R');
  var U := count_char(commands, 'U');
  var D := count_char(commands, 'D');
  var total := 0;
  var i := 0;
  while i < |commands|
    invariant 0 <= i <= |commands|
    invariant total == i
  {
    if commands[i] == 'L' {
      total := total + 1;
    } else if commands[i] == 'R' {
      total := total + 1;
    } else if commands[i] == 'U' {
      total := total + 1;
    } else if commands[i] == 'D' {
      total := total + 1;
    }
    i := i + 1;
  }
  // Since ValidCommands holds, each iteration adds 1
  assert total == |commands| == L + R + U + D;
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
  CountCharNonnegative(commands, 'L');
  CountCharNonnegative(commands, 'R');
  CountCharNonnegative(commands, 'U');
  CountCharNonnegative(commands, 'D');
  ExprLeqN(commands);
  result := 2 * min(count_char(commands, 'L'), count_char(commands, 'R')) + 
            2 * min(count_char(commands, 'U'), count_char(commands, 'D'));
}
// </vc-code>

