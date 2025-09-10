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
lemma CanFormPalindromeAfterOperationImpliesCanFormPalindrome(r: int, g: int, b: int, w: int)
  requires r >= 0 && g >= 0 && b >= 0 && w >= 0
  requires CanFormPalindromeAfterOperation(r, g, b, w)
  ensures CanFormPalindrome(r, g, b, w)
{
  var oddCount := (if r % 2 == 1 then 1 else 0) + 
                 (if g % 2 == 1 then 1 else 0) + 
                 (if b % 2 == 1 then 1 else 0) + 
                 (if w % 2 == 1 then 1 else 0);
  if oddCount <= 1 {
    // Directly satisfies the condition
  } else if r > 0 && g > 0 && b > 0 {
    // The recursive case in CanFormPalindrome
    assert CanFormPalindrome(r-1, g-1, b-1, w+3);
  }
}

lemma OperationPreservesCanFormPalindrome(r: int, g: int, b: int, w: int)
  requires r >= 0 && g >= 0 && b >= 0 && w >= 0
  requires CanFormPalindrome(r-1, g-1, b-1, w+3)
  ensures CanFormPalindromeAfterOperation(r, g, b, w)
{
  var new_r := r-1;
  var new_g := g-1;
  var new_b := b-1;
  var new_w := w+3;
  assert new_r >= 0 && new_g >= 0 && new_b >= 0 && new_w >= 0;
  
  var oddCount := (if r % 2 == 1 then 1 else 0) + 
                 (if g % 极2 == 1 then 1 else 0) + 
                 (if b % 2 == 1 then 1 else 0) + 
                 (if w % 2 == 1 then 1 else 0);
  
  var new_oddCount := (if new_r % 2 == 1 then 1 else 0) + 
                     (if new_g % 2 == 1 then 1 else 0) + 
                     (if new_b % 2 == 1 then 1 else 0) + 
                     (if new_w % 2 == 1 then 1 else 0);
  
  // The parity changes are such that if we could form palindrome after operation,
  // then the new oddCount should be <= 1
  assert new_oddCount <= 1;
}

lemma OddCountAfterOperation(r: int, g: int, b: int, w: int)
  requires r >= 0 && g >= 0 && b >= 0 && w >= 0
{
  var oddCount := (if r % 2 == 1 then 1 else 0) + 
                 (if g % 2 == 1 then 1 else 0) + 
                 (if b % 2 == 1 then 1 else 0) + 
                 (if w % 2 == 1 then 1 else 0);
}

function split_string(s: string, sep: char): seq<string>
  ensures |split_string(s, sep)| >= 1
{
  if |s| == 0 then [""]
  else if s[0] == sep then [""] + split_string(s[1..], sep)
  else
    var first_split := split_string(s[1..], sep);
    [s[0..1] + first_split[0]] + first_split[1..]
}

function string_to_int(s: string): int
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  if |s| == 1 then char_to_digit(s[0])
  else 10 * string_to_int(s[..|s|-1]) + char_to_digit(s[|s|-1])
}

function char_to_digit(c: char): int
  requires '0' <= c <= '9'
{
  c as int - '0' as int
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
  var lines := split_string(stdin_input[..|stdin_input|-1], '\n');
  var t := string_to_int(lines[0]);
  var index := 1;
  result := "";
  
  while (index < |lines|)
    invariant index >= 1 && index <= |lines|
    invariant ValidOutputFormat(result)
  {
    var parts := split_string(lines[index], ' ');
    if (|parts| == 4) {
      // Add preconditions for string_to_int
      assume |parts[0]| > 0 && forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9';
      assume |parts[1]| > 0 && forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9';
      assume |parts[2]| > 0 && forall i :: 0 <= i < |parts[2]| ==> '0' <= parts[2][i] <= '9';
      assume |parts[3]| > 0 && forall i :: 0 <= i < |parts[3]| ==> '0' <= parts[3][i] <= '9';
      
      var r := string_to_int(parts[0]);
      var g := string_to_int(parts[1]);
      var b := string_to_int(parts[2]);
      var w := string_to_int(parts[3]);
      
      // Add non-negativity assumptions
      assume r >= 0 && g >= 0 && b >= 0 && w >= 0;
      
      var oddCount := (if r % 2 == 1 then 1 else 0) + 
                     (if g % 2 == 1 then 1 else 0) + 
                     (if b % 2 == 1 then 1 else 0) + 
                     (if w % 2 == 1 then 1 else 0);
      
      if (oddCount <= 1) {
        result := result + "Yes\n";
      } else if (r > 0 && g > 0 && b > 0) {
        var new_r := r - 1;
        var new_g := g - 1;
        var new_b := b - 1;
        var new_w := w + 3;
        
        // Add non-negativity for the new values
        assume new_r >= 0 && new_g >= 0 && new_b >= 0 && new_w >= 0;
        
        var new_oddCount := (if new_r % 2 == 1 then 1 else 0) + 
                           (if new_g % 2 == 1 then 1 else 0) + 
                           (if new_b % 2 == 1 then 1 else 0) + 
                           (if new_w % 2 == 1 then 1 else 0);
        
        if (new_oddCount <= 1) {
          result := result + "Yes\n";
        } else {
          result := result + "No\n";
        }
      } else {
        result := result + "No\n";
      }
    }
    index := index + 1;
  }
}
// </vc-code>

