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
function powerOf10(p: nat): real
  ensures p > 0 ==> 1.0 < powerOf10(p)
  ensures p == 0 ==> powerOf10(p) == 1.0
{
  if p == 0 then 1.0 else 10.0 * powerOf10(p - 1)
}

/* helper modified by LLM (iteration 2): [Fixed compilation error by removing invalid 'string()' constructor calls.] */
function natToString(n: nat): (res: string)
  ensures forall c :: c in res ==> '0' <= c <= '9'
  ensures |res| > 0
  ensures n == 0 <==> res == "0"
  ensures n > 0 ==> res[0] != '0'
{
  if n == 0 then "0"
  else if n < 10 then [('0' as int + n) as char]
  else natToString(n / 10) + [('0' as int + (n % 10)) as char]
}

/* helper modified by LLM (iteration 4): [Fixed compilation errors (if-then-else, let-in, Seq()) and inconsistent logic in suppress_small.] */
function realToString(r: real, precision: nat, suppress_small: bool): (res: string)
  requires precision > 0
  ensures allCharsAllowed(res)
{
  if r < 0.0 then
    "-" + realToString(-r, precision, suppress_small)
  else
    let p10 := powerOf10(precision) in
    if suppress_small && r > 0.0 && r * p10 < 1.0 then
      "0." + Seq(precision, _ => '0')
    else
      let ipart := Trunc(r) in
      let fpart_scaled := Trunc((r - (ipart as real)) * p10) in
      let ipart_s := natToString(ipart) in
      let fpart_s := natToString(fpart_scaled) in
      let padding_len := if precision > |fpart_s| then precision - |fpart_s| else 0 in
      let padded_fpart_s := Seq(padding_len, _ => '0') + fpart_s in
      ipart_s + "." + padded_fpart_s
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
  /* code modified by LLM (iteration 4): [No logical change; fix was in helper functions.] */
  if |arr| == 0 {
    result := "array([])";
    return;
  }

  var s: string := "array([";
  var i: nat := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant startsWith(s, "array([")
    invariant allCharsAllowed(s)
    invariant i > 0 ==> contains(s, ',')
    invariant |arr| == 1 ==> !contains(s, ',')
  {
    var val_str := realToString(arr[i], precision, suppress_small);
    s := s + val_str;
    if i < |arr| - 1 {
      s := s + ", ";
    }
    i := i + 1;
  }
  result := s + "])";
}
// </vc-code>
