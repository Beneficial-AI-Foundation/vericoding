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
function findNewline(s: string): nat
  requires exists p :: 0 <= p < |s| && s[p] == '\n'
  ensures 0 <= result < |s|
  ensures s[result] == '\n'
  ensures forall q :: 0 <= q < |s| ==> q < result ==> s[q] != '\n'
{
  if s[0] == '\n' then 0 else findNewline(s[1..]) + 1
}

function stringToInt(s: string): nat
  requires ValidDigitString(s)
{
  if |s| == 0 then 0 else 10 * stringToInt(s[0..|s|-1]) + ((s[|s|-1] as int) - ('0' as int))
}

function toDigits(n: int): string
  requires n >= 0
  ensures |result| > 0
  ensures forall i :: 0 <= i < |result| ==> '0' <= result[i] <= '9'
{
  if n == 0 then "0" else toDigitsHelper(n)
}

function toDigitsHelper(n: int): string
  requires n > 0
  decreases n
{
  var remainder := n % 10;
  var digit := (remainder + ('0' as int)) as char;
  var higher := n / 10;
  if higher == 0 then [digit] else toDigitsHelper(higher) + [digit]
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var pos := findNewline(stdin_input);
  var S := stdin_input[0..pos];
  var M_part := stdin_input[pos+1..];
  var mInt := stringToInt(M_part);
  var len := |S| as int;
  var count := 0;
  var shift := 0;
  while shift < len
    invariant 0 <= shift <= len
    invariant count >= 0
  {
    if isGoodShift(S, shift) && cyclicShiftRemainder(S, shift, mInt) == 0 {
      count := count + 1;
    }
    shift := shift + 1;
  }
  result := toDigits(count);
}
// </vc-code>

