predicate ValidInput(input: string)
{
  |input| > 0 &&
  (exists i :: 0 < i < |input| && input[i] == '\n') &&
  (forall i :: 0 <= i < |input| ==> input[i] == '\n' || ('0' <= input[i] <= '9') || ('a' <= input[i] <= 'z')) &&
  (exists i :: 0 < i < |input| && input[i] == '\n' && (forall j :: 0 <= j < i ==> '0' <= input[j] <= '9'))
}

predicate ValidParsedInput(a: int, s: string)
{
  2800 <= a < 5000 &&
  1 <= |s| <= 10 &&
  (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z')
}

predicate CorrectOutput(a: int, s: string, result: string)
{
  (a >= 3200 ==> result == s + "\n") &&
  (a < 3200 ==> result == "red\n")
}

// <vc-helpers>
function parseInput(input: string): (int, string)
  requires ValidInput(input)
{
  var newlineIndex := FindNewline(input);
  var numberPart := input[0..newlineIndex];
  var stringPart := input[newlineIndex+1..];
  (StringToInt(numberPart), stringPart)
}

function FindNewline(input: string): int
  requires ValidInput(input)
  ensures 0 < FindNewline(input) < |input|
  ensures input[FindNewline(input)] == '\n'
  ensures forall j :: 0 <= j < FindNewline(input) ==> '0' <= input[j] <= '9'
{
  var i :| 0 < i < |input| && input[i] == '\n' && (forall j :: 0 <= j < i ==> '0' <= input[j] <= '9');
  i
}

function StringToInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures 0 <= StringToInt(s)
{
  if |s| == 1 then
    s[0] as int - '0' as int
  else
    StringToInt(s[0..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

lemma StringToIntCorrectness(s: string)
  requires |s| == 4
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToInt(s) == (s[0] as int - '0' as int) * 1000 + 
                           (s[1] as int - '0' as int) * 100 + 
                           (s[2] as int - '0' as int) * 10 + 
                           (s[3] as int - '0' as int)
{
  var s3 := s[0..3];
  var s2 := s[0..2];
  var s1 := s[0..1];
  
  assert StringToInt(s1) == s[0] as int - '0' as int;
  assert StringToInt(s2) == StringToInt(s1) * 10 + (s[1] as int - '0' as int);
  assert StringToInt(s3) == StringToInt(s2) * 10 + (s[2] as int - '0' as int);
  assert StringToInt(s) == StringToInt(s3) * 10 + (s[3] as int - '0' as int);
}

lemma StringToIntBounds(s: string)
  requires |s| == 4
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  requires var d0 := s[0] as int - '0' as int;
           var d1 := s[1] as int - '0' as int;
           (d0 >= 3) || (d0 == 2 && d1 >= 8)
  ensures 2800 <= StringToInt(s) < 5000
{
  var d0 := s[0] as int - '0' as int;
  var d1 := s[1] as int - '0' as int;
  var d2 := s[2] as int - '0' as int;
  var d3 := s[3] as int - '0' as int;
  
  assert 0 <= d0 <= 9;
  assert 0 <= d1 <= 9;
  assert 0 <= d2 <= 9;
  assert 0 <= d3 <= 9;
  
  StringToIntCorrectness(s);
  var result := d0 * 1000 + d1 * 100 + d2 * 10 + d3;
  assert StringToInt(s) == result;
  
  if d0 >= 3 {
    assert 3000 <= result <= 3999;
    assert 2800 <= result < 5000;
  } else if d0 == 2 && d1 >= 8 {
    assert 2800 <= result <= 2999;
    assert 2800 <= result < 5000;
  }
}

lemma ParseInputProperties(input: string)
  requires ValidInput(input)
  requires var newlineIndex := FindNewline(input); 
           newlineIndex == 4 && |input| >= 6 && |input| <= 16
  requires var newlineIndex := FindNewline(input);
           var stringPart := input[newlineIndex+1..];
           forall j :: 0 <= j < |stringPart| ==> 'a' <= stringPart[j] <= 'z'
  requires var newlineIndex := FindNewline(input);
           var numberPart := input[0..newlineIndex];
           var d0 := numberPart[0] as int - '0' as int;
           var d1 := numberPart[1] as int - '0' as int;
           (d0 >= 3) || (d0 == 2 && d1 >= 8)
  ensures var (a, s) := parseInput(input); ValidParsedInput(a, s)
{
  var newlineIndex := FindNewline(input);
  var numberPart := input[0..newlineIndex];
  var stringPart := input[newlineIndex+1..];
  var a := StringToInt(numberPart);
  
  assert |numberPart| == 4;
  StringToIntBounds(numberPart);
  assert 2800 <= a < 5000;
  assert 1 <= |stringPart| <= 10;
  assert forall j :: 0 <= j < |stringPart| ==> 'a' <= stringPart[j] <= 'z';
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
  requires ValidInput(input)
  requires exists a: int, s: string :: 
    parseInput(input) == (a, s) && ValidParsedInput(a, s)
  ensures exists a: int, s: string :: 
    parseInput(input) == (a, s) && 
    ValidParsedInput(a, s) &&
    CorrectOutput(a, s, result)
  ensures |result| > 0
  ensures result[|result|-1] == '\n'
  ensures (exists a: int, s: string :: 
    parseInput(input) == (a, s) && a >= 3200) ==> 
    (exists s: string :: result == s + "\n" && 1 <= |s| <= 10 && (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z'))
  ensures (exists a: int, s: string :: 
    parseInput(input) == (a, s) && a < 3200) ==> result == "red\n"
// </vc-spec>
// <vc-code>
{
  var newlineIndex := FindNewline(input);
  var numberPart := input[0..newlineIndex];
  var stringPart := input[newlineIndex+1..];
  
  var (a, s) := parseInput(input);
  
  assert a == StringToInt(numberPart);
  assert s == stringPart;
  
  if a >= 3200 {
    result := s + "\n";
  } else {
    result := "red\n";
  }
}
// </vc-code>

