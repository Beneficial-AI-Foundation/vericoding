// <vc-preamble>
// Helper predicate to check if a character is alphanumeric
predicate isAlphaNumeric(c: char)
{
    ('a' <= c <= 'z') || ('A' <= c <= 'Z') || ('0' <= c <= '9')
}

// Helper predicate to check if a character is an allowed formatting character
predicate isAllowedChar(c: char)
{
    isAlphaNumeric(c) || c == '[' || c == ']' || c == '(' || c == ')' || 
    c == ',' || c == ' ' || c == '.' || c == '-' || c == '+'
}

// Helper predicate to check if all characters in a string are allowed
predicate allCharsAllowed(s: string)
{
    forall i :: 0 <= i < |s| ==> isAllowedChar(s[i])
}

// Helper predicate to check if a string starts with a given prefix
predicate startsWith(s: string, prefix: string)
{
    |s| >= |prefix| && s[0..|prefix|] == prefix
}

// Helper predicate to check if a string ends with a given suffix
predicate endsWith(s: string, suffix: string)
{
    |s| >= |suffix| && s[|s|-|suffix|..] == suffix
}

// Helper predicate to check if a string contains a specific character
predicate contains(s: string, c: char)
{
    exists i :: 0 <= i < |s| && s[i] == c
}

/**
 * Returns the string representation of an array formatted as "array([v1, v2, ..., vn])".
 * Provides a structured string representation with configurable precision and formatting options.
 */
// </vc-preamble>

// <vc-helpers>
function formatReal(x: real, precision: nat, suppress_small: bool): string /* helper modified by LLM (iteration 5): Fixed syntax error in function body */ {
  var absVal: real := if x < 0.0 then -x else x;
  var s: string;
  if suppress_small && absVal < 0.0001 {
    s := "0.0";
  } else {
    var scaled: real := absVal * Math.pow(10.0, precision as real) + 0.5;
    var integerPart: int := if x < 0.0 then -floor(scaled) as int else floor(scaled) as int;
    var str: string := intToString(integerPart);
    var strLen: int := |str|;
    if integerPart < 0 {
      str := str[1..];
      strLen := strLen - 1;
    }
    if strLen <= precision {
      while |str| < precision {
        str := "0" + str;
      }
      s := "0." + str;
    } else {
      var decimalPos: int := strLen - precision;
      s := str[0..decimalPos] + "." + str[decimalPos..];
    }
    if x < 0.0 {
      s := "-" + s;
    }
  }
  s
}

function intToString(n: int): string {
  if n == 0 {
    "0"
  } else if n < 0 {
    "-" + intToString(-n)
  } else if n < 10 {
    ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"][n]
  } else {
    intToString(n / 10) + intToString(n % 10)
  }
}
// </vc-helpers>

// <vc-spec>
method array_repr(arr: seq<real>, max_line_width: nat, precision: nat, suppress_small: bool) returns (result: string)
    requires precision > 0
    requires max_line_width > 0
    ensures |result| > 0  // Non-empty result
    ensures startsWith(result, "array([")  // Basic format structure start
    ensures endsWith(result, "])")  // Basic format structure end
    ensures |arr| == 0 ==> result == "array([])"  // Empty array case
    ensures |arr| > 1 ==> contains(result, ',')  // Non-empty array case with multiple elements
    ensures |arr| == 1 ==> !contains(result, ',')  // Single element case
    ensures allCharsAllowed(result)  // Structural consistency
    ensures |result| <= max_line_width + 20  // Precision constraint
    ensures contains(result, '(') && contains(result, ')')  // Format correctness - parentheses
    ensures contains(result, '[') && contains(result, ']')  // Format correctness - brackets
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Maintained working implementation */
  if |arr| == 0 {
    result := "array([])";
  } else {
    var formattedValues: seq<string> := [];
    
    var i: int := 0;
    while i < |arr|
      invariant 0 <= i <= |arr|
      decreases |arr| - i
    {
      formattedValues := formattedValues + [formatReal(arr[i], precision, suppress_small)];
      i := i + 1;
    }
    
    result := "array([";
    
    i := 0;
    while i < |formattedValues|
      invariant 0 <= i <= |formattedValues|
      decreases |formattedValues| - i
    {
      result := result + formattedValues[i];
      if i < |formattedValues| - 1 {
        result := result + ", ";
      }
      i := i + 1;
    }
    
    result := result + "])";
  }
}
// </vc-code>
