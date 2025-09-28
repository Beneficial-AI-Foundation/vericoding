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
/* helper modified by LLM (iteration 2): fixed function method syntax and expression */
function SplitStringExec(s: string, sep: string): seq<string>
  requires sep != ""
{
  var res := [];
  var start := 0;
  var i := 0;
  while i <= |s| - |sep|
  {
    if s[i..i+|sep|] == sep {
      res := res + [s[start..i]];
      start := i + |sep|;
      i := i + |sep|;
    } else {
      i := i + 1;
    }
  }
  res := res + [s[start..]];
  res
}

/* helper modified by LLM (iteration 2): fixed function method syntax */
function TrimStringExec(s: string): string
{
  var start := 0;
  while start < |s| && s[start] == ' ' {
    start := start + 1;
  }
  var end := |s|;
  while end > start && s[end-1] == ' ' {
    end := end - 1;
  }
  s[start..end]
}

/* helper modified by LLM (iteration 2): fixed function method syntax */
predicate IsNumericStringExec(s: string)
{
  if |s| == 0 then false else
  var hasDot := false;
  var i := 0;
  if s[0] == '-' || s[0] == '+' {
    i := 1;
  }
  while i < |s|
  {
    if s[i] == '.' {
      if hasDot then return false;
      hasDot := true;
    } else if '0' <= s[i] <= '9' {
      // valid
    } else {
      return false;
    }
    i := i + 1;
  }
  true
}

/* helper modified by LLM (iteration 2): fixed function method syntax */
function StringToRealExec(s: string): real
  requires IsNumericStringExec(s)
{
  var sign := 1.0;
  var i := 0;
  if s[0] == '-' {
    sign := -1.0;
    i := 1;
  } else if s[0] == '+' {
    i := 1;
  }
  var value := 0.0;
  var afterDot := false;
  var fractionalPlace := 0.1;
  while i < |s|
  {
    if s[i] == '.' {
      afterDot := true;
      i := i + 1;
    } else {
      var digit := (s[i] - '0') as real;
      if afterDot {
        value := value + digit * fractionalPlace;
        fractionalPlace := fractionalPlace * 0.1;
      } else {
        value := value * 10.0 + digit;
      }
      i := i + 1;
    }
  }
  sign * value
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
{
  /* code modified by LLM (iteration 2): fixed loop bounds and invariants */
  var tokens := SplitStringExec(input, sep);
  result := new real[n];
  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> 
      result[j] == StringToRealExec(TrimStringExec(tokens[j]))
  {
    var token := tokens[i];
    var trimmed := TrimStringExec(token);
    result[i] := StringToRealExec(trimmed);
  }
}
// </vc-code>
