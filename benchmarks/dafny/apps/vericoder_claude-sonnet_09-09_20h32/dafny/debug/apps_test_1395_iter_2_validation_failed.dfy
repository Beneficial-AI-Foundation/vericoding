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
function FindNewlineIndex(s: string): int
  requires |s| > 0
  requires exists pos :: 0 <= pos < |s| && s[pos] == '\n'
  ensures 0 <= FindNewlineIndex(s) < |s|
  ensures s[FindNewlineIndex(s)] == '\n'
{
  if s[0] == '\n' then 0
  else 1 + FindNewlineIndex(s[1..])
}

function ExtractNumberString(stdin_input: string): string
  requires ValidInput(stdin_input)
  requires forall i :: 0 <= i < |stdin_input| && stdin_input[i] != '\n' ==> '0' <= stdin_input[i] <= '9'
  requires exists pos :: 0 <= pos < |stdin_input| && stdin_input[pos] == '\n' && pos > 0
  ensures ValidDigitString(ExtractNumberString(stdin_input))
{
  var newline_pos := FindNewlineIndex(stdin_input);
  stdin_input[0..newline_pos]
}

function FindMinShift(s: string, current_shift: int, min_shift: int, min_remainder: int): int
  requires ValidDigitString(s)
  requires |s| > 0
  requires 0 <= current_shift <= |s|
  requires 0 <= min_shift < |s|
  requires 0 <= min_remainder < |s|
  requires |s| >= 2
  ensures 0 <= FindMinShift(s, current_shift, min_shift, min_remainder) < |s|
  decreases |s| - current_shift
{
  if current_shift == |s| then min_shift
  else if isGoodShift(s, current_shift) then
    var remainder := cyclicShiftRemainder(s, current_shift, |s|);
    if remainder < min_remainder then
      FindMinShift(s, current_shift + 1, current_shift, remainder)
    else
      FindMinShift(s, current_shift + 1, min_shift, min_remainder)
  else
    FindMinShift(s, current_shift + 1, min_shift, min_remainder)
}

function BuildShiftedString(s: string, shift: int, pos: int): string
  requires ValidDigitString(s)
  requires |s| > 0
  requires 0 <= shift < |s|
  requires 0 <= pos <= |s|
  ensures pos < |s| ==> ValidOutput(BuildShiftedString(s, shift, pos))
  ensures pos == |s| ==> BuildShiftedString(s, shift, pos) == ""
  decreases |s| - pos
{
  if pos == |s| then ""
  else
    var idx := (shift + pos) % |s|;
    [s[idx]] + BuildShiftedString(s, shift, pos + 1)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  assume forall i :: 0 <= i < |stdin_input| && stdin_input[i] != '\n' ==> '0' <= stdin_input[i] <= '9';
  assume exists pos :: 0 <= pos < |stdin_input| && stdin_input[pos] == '\n' && pos > 0;
  
  var number_string := ExtractNumberString(stdin_input);
  
  if |number_string| == 1 {
    result := number_string;
  } else {
    var first_good_shift := if isGoodShift(number_string, 0) then 0 else 1;
    var first_remainder := cyclicShiftRemainder(number_string, first_good_shift, |number_string|);
    var best_shift := FindMinShift(number_string, 0, first_good_shift, first_remainder);
    result := BuildShiftedString(number_string, best_shift, 0);
  }
}
// </vc-code>

