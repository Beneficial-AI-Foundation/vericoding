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
function method ParseInput(input: string): (r: int, g: int, b: int, w: int)
  requires ValidInput(input)
  ensures r >= 0 && g >= 0 && b >= 0 && w >= 0
{
  var parts := input.Split(' ');
  assert |parts| == 5; // Expected format: r g b w\n
  var r_str := parts[0];
  var g_str := parts[1];
  var b_str := parts[2];
  var w_str := parts[3];

  var r_val := StringToInt(r_str);
  var g_val := StringToInt(g_str);
  var b_val := StringToInt(b_str);
  var w_val := StringToInt(w_str);

  (r_val, g_val, b_val, w_val)
}

function method StringToInt(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToInt(s) >= 0
{
  var n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n >= 0
    invariant n == (if i == 0 then 0 else StringToInt(s[..i]))
  {
    n := n * 10 + (s[i] - '0');
    i := i + 1;
  }
  n
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
    var (r_str, g_str, b_str, w_str, _) := stdin_input.Split(' ');

    var r := StringToInt(r_str);
    var g := StringToInt(g_str);
    var b := StringToInt(b_str);
    var w := StringToInt(w_str.Substring(0, |w_str|-1)); // Remove newline

    if CanFormPalindrome(r, g, b, w) then
        result := "Yes\n";
    else
        result := "No\n";
}
// </vc-code>

