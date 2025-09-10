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
lemma count_char_additive(s: string, t: string, c: char)
  ensures count_char(s + t, c) == count_char(s, c) + count_char(t, c)
{
  if s == "" {
    calc {
      count_char(s + t, c);
      count_char(t, c);
      count_char(s, c) + count_char(t, c);
    }
  } else {
    calc {
      count_char(s + t, c);
      (if (s+t)[0] == c then 1 else 0) + count_char((s+t)[1..], c);
      { 
        assert (s+t)[0] == s[0];
        assert (s+t)[1..] == s[1..] + t;
      }
      (if s[0] == c then 1 else 0) + count_char(s[1..] + t, c);
      (if s[0] == c then 1 else 0) + (count_char(s[1..], c) + count_char(t, c));
        by {
          count_char_additive(s[1..], t, c);
        }
      count_char(s, c) + count_char(t, c);
    }
  }
}

lemma count_char_prefix(s: string, c: char, i: int)
    requires 0 <= i <= |s|
    ensures count_char(s, c) == count_char(s[0..i], c) + count_char(s[i..], c)
{
    calc {
        count_char(s, c);
        count_char(s[0..i] + s[i..], c);
        count_char(s[0..i], c) + count_char(s[i..], c);
          by {
            count_char_additive(s[0..i], s[i..], c);
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
  result := 2 * min(L, R) + 2 * min(U, D);
}
// </vc-code>

