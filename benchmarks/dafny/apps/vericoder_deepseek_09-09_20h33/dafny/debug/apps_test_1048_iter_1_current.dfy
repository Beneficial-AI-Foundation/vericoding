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
lemma MinSumLemma(a: int, b: int, c: int, d: int)
  ensures 2 * min(a, b) + 2 * min(c, d) <= a + b + c + d
{
  assert min(a, b) <= a && min(a, b) <= b;
  assert min(c, d) <= c && min(c, d) <= d;
  assert 2 * min(a, b) <= a + b;
  assert 2 * min(c, d) <= c + d;
}

lemma CountCharValid(commands: string, c: char)
  requires ValidCommands(commands)
  requires c in {'L', 'R', 'U', 'D'}
  ensures 0 <= count_char(commands, c) <= |commands|
{
  // Dafny can prove this by induction automatically
}

lemma MinNonNegative(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures min(a, b) >= 0
{
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
  var lCount := count_char(commands, 'L');
  var rCount := count_char(commands, 'R');
  var uCount := count_char(commands, 'U');
  var dCount := count_char(commands, 'D');
  
  assert lCount >= 0 && rCount >= 0 && uCount >= 0 && dCount >= 0;
  
  var minLR := min(lCount, rCount);
  var minUD := min(uCount, dCount);
  
  result := 2 * minLR + 2 * minUD;
  
  assert result % 2 == 0;
}
// </vc-code>

