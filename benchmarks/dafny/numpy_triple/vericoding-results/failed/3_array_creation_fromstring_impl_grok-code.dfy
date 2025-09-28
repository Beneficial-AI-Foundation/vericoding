// <vc-preamble>
// Helper function to represent string splitting (ghost function for specification)
ghost function {:axiom} SplitString(s: string, sep: string): seq<string>
  requires sep != ""
  ensures |SplitString(s, sep)| >= 1

// Helper function to represent string trimming
ghost function TrimString(s: string): string

// Helper function to check if a string represents a valid number
ghost predicate IsNumericString(s: string)

// Helper function to convert a valid numeric string to a real number
ghost function StringToReal(s: string): real
  requires IsNumericString(s)

// Main method specification for fromstring
// </vc-preamble>

// <vc-helpers>
method SplitString(s: string, sep: string) returns (tokens: seq<string>)
  requires sep != ""
  ensures |tokens| >= 1
{
  tokens := [];
  var start := 0;
  var lenS := |s|;
  var lenSep := |sep|;
  while (start < lenS)
    invariant 0 <= start <= lenS
    invariant |tokens| >= 0
  {
    var idx := IndexOf(s[start..], sep);
    if idx == -1 {
      tokens := tokens + [s[start..lenS]];
      break;
    } else {
      tokens := tokens + [s[start..start+idx]];
      start := start + idx + lenSep;
    }
    if !(|tokens| >= 0) { break; } // Weak, but for now
  }
  if (|tokens| == 0) {
    tokens := tokens + [""];
  }
}

/* helper modified by LLM (iteration 2): Fixed IndexOf to be a method and syntax corrected */
method IndexOf(haystack: seq<char>, needle: seq<char>) returns (idx: int)
{
  if |needle| == 0 || |needle| > |haystack| {
    idx := -1;
  } else if haystack[..|needle|] == needle {
    idx := 0;
  } else {
    var subIdx := IndexOf(haystack[1..], needle);
    idx := 1 + subIdx;
  }
}

method TrimString(s: string) returns (trimmed: string)
{
  var start := 0;
  while (start < |s| && s[start] == ' ') { start := start + 1; }
  var end := |s|;
  while (end > start && s[end-1] == ' ') { end := end - 1; }
  trimmed := s[start..end];
}

method IsNumericString(s: string) returns (isNum: bool)
{
  if |s| == 0 { isNum := false; return; }
  isNum := true;
  var hasDot := false;
  for i := 0 to |s|
  {
    var c := s[i];
    if c == '.' {
      if hasDot { isNum := false; return; }
      hasDot := true;
    } else if c < '0' || c > '9' {
      if !(i == 0 && c == '-') { isNum := false; return; }
    }
  }
}

method StringToReal(s: string) returns (result: real)
  requires IsNumericString(s)
{
  result := 0.0;
  var i := 0;
  var sign := 1.0;
  if |s| > 0 && s[0] == '-' {
    sign := -1.0;
    i := 1;
  }
  var dotPos := -1;
  var fracDigits := 0;
  for j := i to |s|
  {
    if s[j] == '.' {
      dotPos := j;
    }
  }
  for j := i to |s|
  {
    if s[j] == '.' { dotPos := j; continue; }
    var digit := s[j] - '0';
    if digit < 0 || digit > 9 { continue; }
    fracDigits := fracDigits + (if dotPos != -1 then 1 else 0);
    result := result * 10.0 + (digit as real);
  }
  if dotPos != -1 {
    result := result / Pow10(fracDigits);
  }
  result := result * sign;
}

function Pow10(exp: nat): real
{
  if exp == 0 then 1.0 else 10.0 * Pow10(exp - 1)
}
// </vc-helpers>

// <vc-spec>
method FromString(input: string, sep: string, n: nat) returns (result: seq<real>)
  requires sep != ""
  requires n > 0
  requires var tokens := SplitString(input, sep);
           |tokens| == n
  requires var tokens := SplitString(input, sep);
           |tokens| > 0 &&
           (forall i :: 0 <= i < |tokens| ==> TrimString(tokens[i]) != "") &&
           (forall i :: 0 <= i < |tokens| ==> IsNumericString(TrimString(tokens[i])))
  
  ensures |result| == n
  
  ensures var tokens := SplitString(input, sep);
          forall i :: 0 <= i < |result| ==>
            result[i] == StringToReal(TrimString(tokens[i]))
  
  // Example behaviors from NumPy documentation
  ensures input == "1 2" && sep == " " && n == 2 ==>
          result[0] == 1.0 && result[1] == 2.0
  
  ensures input == "1, 2" && sep == "," && n == 2 ==>
          result[0] == 1.0 && result[1] == 2.0
  
  // Result contains no NaN values
  ensures forall i :: 0 <= i < |result| ==> result[i] == result[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implemented the method body calling helper methods */
{
  var tokens := SplitString(input, sep);
  result := [];
  for i := 0 to n
    invariant 0 <= i <= n
    invariant |result| == i
  {
    var trimmed := TrimString(tokens[i]);
    var isNum := IsNumericString(trimmed);
    assert isNum;
    var num := StringToReal(trimmed);
    result := result + [num];
  }
}
// </vc-code>
