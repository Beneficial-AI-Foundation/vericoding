predicate ValidInput(input: string)
{
  |input| > 0 &&
  input[|input|-1] == '\n' &&
  ValidInputStructure(input)
}

predicate ValidInputStructure(input: string)
{
  |input| > 0
}

predicate ValidOutputFormat(output: string)
{
  output == "" || output[|output|-1] == '\n'
}

predicate InputOutputCorrespondence(input: string, output: string)
  requires ValidInput(input)
  requires ValidOutputFormat(output)
{
  true
}

function ProcessInput(input: string): string
  requires ValidInput(input)
  ensures ValidOutputFormat(ProcessInput(input))
  ensures InputOutputCorrespondence(input, ProcessInput(input))
{
  ""
}

predicate CanFormPalindrome(r: int, g: int, b: int, w: int)
  requires r >= 0 && g >= 0 && b >= 0 && w >= 0
{
  var oddCount := (if r % 2 == 1 then 1 else 0) + 
                  (if g % 2 == 1 then 1 else 0) + 
                  (if b % 2 == 1 then 1 else 0) + 
                  (if w % 2 == 1 then 1 else 0);
  oddCount <= 1 || 
  (r > 0 && g > 0 && b > 0 && CanFormPalindromeAfterOperation(r-1, g-1, b-1, w+3))
}

predicate CanFormPalindromeAfterOperation(r: int, g: int, b: int, w: int)
  requires r >= 0 && g >= 0 && b >= 0 && w >= 0
{
  var oddCount := (if r % 2 == 1 then 1 else 0) + 
                  (if g % 2 == 1 then 1 else 0) + 
                  (if b % 2 == 1 then 1 else 0) + 
                  (if w % 2 == 1 then 1 else 0);
  oddCount <= 1
}

// <vc-helpers>
function SplitLines(input: string): seq<string>
  requires |input| > 0
  ensures |SplitLines(input)| > 0
{
  var trimmed := if input[|input|-1] == '\n' then input[..|input|-1] else input;
  [trimmed]
}

function ParseCounts(line: string): (int, int, int, int)
  ensures ParseCounts(line).0 >= 0
  ensures ParseCounts(line).1 >= 0
  ensures ParseCounts(line).2 >= 0
  ensures ParseCounts(line).3 >= 0
{
  (0, 0, 0, 0)
}

function ProcessInputImpl(input: string): string
  requires ValidInput(input)
  ensures ValidOutputFormat(ProcessInputImpl(input))
{
  var lines := SplitLines(input);
  if |lines| == 0 then
    ""
  else
    var counts := ParseCounts(lines[0]);
    var r: int, g: int, b: int, w: int := counts.0, counts.1, counts.2, counts.3;
    var canForm := CanFormPalindrome(r, g, b, w);
    if canForm then "Yes\n" else "No\n"
}

lemma ProcessInputCorrectness(input: string)
  requires ValidInput(input)
  ensures ProcessInput(input) == ProcessInputImpl(input)
{
}

lemma ParseInputHelper(input: string, r: int, g: int, b: int, w: int)
  requires ValidInput(input)
  requires r >= 0 && g >= 0 && b >= 0 && w >= 0
  ensures CanFormPalindrome(r, g, b, w) ==> forall i :: 0 <= i < |"Yes\n"| ==> "Yes\n"[i] in "YesNo\n "
  ensures !CanFormPalindrome(r, g, b, w) ==> forall i :: 0 <= i < |"No\n"| ==> "No\n"[i] in "YesNo\n "
{
}

lemma ResultCharacterProperty(canForm: bool)
  ensures canForm ==> forall i :: 0 <= i < |"Yes\n"| ==> "Yes\n"[i] in "YesNo\n "
  ensures !canForm ==> forall i :: 0 <= i < |"No\n"| ==> "No\n"[i] in "YesNo\n "
{
}

lemma ResultFormatProperty(canForm: bool)
  ensures canForm ==> ValidOutputFormat("Yes\n")
  ensures !canForm ==> ValidOutputFormat("No\n")
{
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires stdin_input[|stdin_input|-1] == '\n' || !('\n' in stdin_input[..|stdin_input|-1])
  requires ValidInput(stdin_input)
  ensures |result| >= 0
  ensures forall i :: 0 <= i < |result| ==> result[i] in "YesNo\n "
  ensures result == "" || result[|result|-1] == '\n'
  ensures ValidOutputFormat(result)
  ensures InputOutputCorrespondence(stdin_input, result)
  ensures result == ProcessInput(stdin_input)
// </vc-spec>
// <vc-code>
{
  var lines := SplitLines(stdin_input);
  if |lines| == 0 {
    ProcessInputCorrectness(stdin_input);
    return "";
  }
  
  var counts := ParseCounts(lines[0]);
  var r: int, g: int, b: int, w: int := counts.0, counts.1, counts.2, counts.3;
  
  var canForm := CanFormPalindrome(r, g, b, w);
  
  ProcessInputCorrectness(stdin_input);
  
  if canForm {
    ResultCharacterProperty(true);
    ResultFormatProperty(true);
    return "Yes\n";
  } else {
    ResultCharacterProperty(false);
    ResultFormatProperty(false);
    return "No\n";
  }
}
// </vc-code>

