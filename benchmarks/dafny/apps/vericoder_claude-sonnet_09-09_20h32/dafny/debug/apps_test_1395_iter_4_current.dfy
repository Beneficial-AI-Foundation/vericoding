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
  ensures ValidDigitString(ExtractNumberString(stdin_input))
{
  var newline_pos := FindNewlineIndex(stdin_input);
  assert newline_pos < |stdin_input|;
  assert newline_pos >= 0;
  assert forall i :: 0 <= i < newline_pos ==> '0' <= stdin_input[i] <= '9';
  stdin_input[0..newline_pos]
}

function FindMinShift(s: string, current_shift: int, min_shift: int, min_remainder: int): int
  requires ValidDigitString(s)
  requires |s| > 0
  requires 0 <= current_shift <= |s|
  requires 0 <= min_shift < |s|
  requires 0 <= min_remainder < |s|
  requires |s| >= 2
  requires isGoodShift(s, min_shift)
  ensures 0 <= FindMinShift(s, current_shift, min_shift, min_remainder) < |s|
  ensures isGoodShift(s, FindMinShift(s, current_shift, min_shift, min_remainder))
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
  ensures |BuildShiftedString(s, shift, pos)| == |s| - pos
  ensures pos == |s| ==> BuildShiftedString(s, shift, pos) == ""
  ensures pos < |s| ==> |BuildShiftedString(s, shift, pos)| > 0
  ensures pos == 0 && isGoodShift(s, shift) ==> |BuildShiftedString(s, shift, pos)| > 0 && BuildShiftedString(s, shift, pos)[0] != '0'
  ensures forall i :: 0 <= i < |BuildShiftedString(s, shift, pos)| ==> '0' <= BuildShiftedString(s, shift, pos)[i] <= '9'
  decreases |s| - pos
{
  if pos == |s| then ""
  else
    var idx := (shift + pos) % |s|;
    [s[idx]] + BuildShiftedString(s, shift, pos + 1)
}

lemma BuildShiftedStringValidOutput(s: string, shift: int)
  requires ValidDigitString(s)
  requires |s| > 0
  requires 0 <= shift < |s|
  requires isGoodShift(s, shift)
  ensures ValidOutput(BuildShiftedString(s, shift, 0))
{
}

function FindFirstGoodShift(s: string, pos: int): int
  requires ValidDigitString(s)
  requires |s| >= 2
  requires 0 <= pos < |s|
  requires exists i :: pos <= i < |s| && isGoodShift(s, i)
  ensures pos <= FindFirstGoodShift(s, pos) < |s|
  ensures isGoodShift(s, FindFirstGoodShift(s, pos))
  decreases |s| - pos
{
  if isGoodShift(s, pos) then pos
  else FindFirstGoodShift(s, pos + 1)
}

lemma ExistsGoodShift(s: string)
  requires ValidDigitString(s)
  requires |s| >= 2
  ensures exists i :: 0 <= i < |s| && isGoodShift(s, i)
{
  if isGoodShift(s, 0) {
    assert exists i :: 0 <= i < |s| && isGoodShift(s, i);
  } else {
    assert s[0] == '0';
    if s[1] != '0' {
      assert isGoodShift(s, 1);
      assert exists i :: 0 <= i < |s| && isGoodShift(s, i);
    } else {
      var j := 2;
      while j < |s| && s[j] == '0'
        invariant 2 <= j <= |s|
        invariant forall k :: 1 <= k < j ==> s[k] == '0'
        decreases |s| - j
      {
        j := j + 1;
      }
      if j < |s| {
        assert s[j] != '0';
        assert isGoodShift(s, j);
        assert exists i :: 0 <= i < |s| && isGoodShift(s, i);
      } else {
        assert forall k :: 1 <= k < |s| ==> s[k] == '0';
        assert false;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires ValidInput(stdin_input)
  ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
  var number_string := ExtractNumberString(stdin_input);
  
  if |number_string| == 1 {
    result := number_string;
  } else {
    ExistsGoodShift(number_string);
    var first_good_shift := FindFirstGoodShift(number_string, 0);
    var first_remainder := cyclicShiftRemainder(number_string, first_good_shift, |number_string|);
    var best_shift := FindMinShift(number_string, 0, first_good_shift, first_remainder);
    BuildShiftedStringValidOutput(number_string, best_shift);
    result := BuildShiftedString(number_string, best_shift, 0);
  }
}
// </vc-code>

