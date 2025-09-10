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
function stringToInt(s: string): int
  requires ValidDigitString(s)
  ensures 0 <= stringToInt(s)
{
  stringToIntHelper(s, 0, 0)
}

function stringToIntHelper(s: string, pos: int, acc: int): int
  requires 0 <= pos <= |s|
  requires ValidDigitString(s)
  ensures 0 <= stringToIntHelper(s, pos, acc)
  decreases |s| - pos
{
  if pos == |s| then acc
  else
    var digit := (s[pos] as int) - ('0' as int);
    stringToIntHelper(s, pos + 1, acc * 10 + digit)
}

function intToString(n: int): string
  requires 0 <= n
  ensures ValidDigitString(intToString(n)) && (|intToString(n)| > 0)
{
  if n == 0 then "0" else intToStringHelper(n, "")
}

function intToStringHelper(n: int, acc: string): string
  requires n > 0
  ensures ValidDigitString(acc + intToStringHelper(n, acc))
  ensures |acc + intToStringHelper(n, acc)| > 0
  decreases n
{
  if n == 0 then acc
  else
    var digit := '0' + ((n % 10) as char);
    intToStringHelper(n / 10, [digit] + acc)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var pos := 0;
  while pos < |stdin_input| && stdin_input[pos] != '\n'
    invariant 0 <= pos <= |stdin_input|
  {
    pos := pos + 1;
  }
  var m_str := stdin_input[..pos];
  var s := stdin_input[pos+1..];
  assume ValidDigitString(m_str);
  assume ValidDigitString(s);
  assume |s| > 0;
  var m := stringToInt(m_str);
  assume m >= 2;
  var shift := 0;
  while shift < |s| && s[shift] == '0'
    invariant 0 <= shift <= |s|
  {
    shift := shift + 1;
  }
  var remainder := if shift == |s| then 0 else cyclicShiftRemainder(s, shift, m);
  var result := intToString(remainder);
}
// </vc-code>

