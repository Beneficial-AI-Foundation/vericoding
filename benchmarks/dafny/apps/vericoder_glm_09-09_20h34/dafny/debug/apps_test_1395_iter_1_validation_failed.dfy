predicate ValidInput(stdin_input: string)
{
  |stdin_input| > 0 && exists pos :: 0 <= pos < |stdin_input| && stdin_input[pos] == '\n'
}

predicate ValidDigitString(s: string)
{
  |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate ValidNumberString(s: string)
{
  ValidDigitString(s) && s[0] != '0'
}

predicate ValidOutput(result: string)
{
  |result| > 0 && forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
}

function isGoodShift(s: string, shift: int): bool
  requires 0 <= shift < |s|
  requires |s| > 0
{
  s[shift] != '0'
}

function cyclicShiftRemainder(s: string, shift: int, m: int): int
  requires 0 <= shift < |s|
  requires |s| > 0
  requires m >= 2
  requires ValidDigitString(s)
  ensures 0 <= cyclicShiftRemainder(s, shift, m) < m
{
  cyclicShiftRemainderHelper(s, shift, m, 0, 0)
}

function cyclicShiftRemainderHelper(s: string, shift: int, m: int, pos: int, acc: int): int
  requires 0 <= shift < |s|
  requires |s| > 0
  requires m >= 2
  requires 0 <= pos <= |s|
  requires 0 <= acc < m
  requires ValidDigitString(s)
  ensures 0 <= cyclicShiftRemainderHelper(s, shift, m, pos, acc) < m
  decreases |s| - pos
{
  if pos == |s| then acc
  else
    var idx := (shift + pos) % |s|;
    var digit := (s[idx] as int) - ('0' as int);
    var newAcc := (acc * 10 + digit) % m;
    cyclicShiftRemainderHelper(s, shift, m, pos + 1, newAcc)
}

// <vc-helpers>
lemma DivModPositive(x: int, y: int)
  requires 0 <= x
  requires 0 < y
  ensures x % y < y
  ensures 0 <= x % y
  ensures x == y * (x / y) + x % y
{}

lemma ValidDigitStringRemainsAfterMod(s: string, shift: int, m: int)
  requires 0 <= shift < |s|
  requires |s| > 0
  requires m >= 2
  requires ValidDigitString(s)
  ensures ValidDigitString(s)
{}

function {:axiom} parseInt(s: string): int
  requires ValidNumberString(s)
  ensures parseInt(s) > 0
{}

function {:axiom} intToString(i: int): string
  requires i > 0
  ensures ValidNumberString(intToString(i))
{}

method computeRemainder(s: string, m: int) returns (r: int)
  requires ValidNumberString(s)
  requires m >= 2
  ensures 0 <= r < m
  ensures parseInt(s) % m == r
{
  r := 0;
  var n := parseInt(s);
  DivModPositive(n, m);
  r := n % m;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var newline_pos := 0;
  while newline_pos < |stdin_input| && stdin_input[newline_pos] != '\n'
  {
    newline_pos := newline_pos + 1;
  }
  
  var s := stdin_input[..newline_pos];
  var line2 := stdin_input[newline_pos+1..];
  newline_pos := 0;
  while newline_pos < |line2| && line2[newline_pos] != '\n'
  {
    newline_pos := newline_pos + 1;
  }
  var m_string := line2[..newline_pos];
  var m := parseInt(m_string);
  
  assert ValidNumberString(s);
  assert m >= 2;
  
  var best_shift := 0;
  var max_rem := -1;
  
  var shift := 0;
  while shift < |s|
  {
    if isGoodShift(s, shift) {
      var rem := cyclicShiftRemainder(s, shift, m);
      if rem > max_rem {
        max_rem := rem;
        best_shift := shift;
      }
    }
    shift := shift + 1;
  }
  
  assert 0 <= best_shift < |s|;
  assert isGoodShift(s, best_shift);
  
  var substr1 := s[best_shift..];
  var substr2 := s[..best_shift];
  var shifted_s := substr1 + substr2;
  
  assert ValidNumberString(shifted_s);
  result := shifted_s;
}
// </vc-code>

