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
/* helper modified by LLM (iteration 5): fix function syntax compilation errors */
function ConvertToReal(s: string): real
  requires IsNumericString(TrimString(s))
  ensures ConvertToReal(s) == StringToReal(TrimString(s))
{
  StringToReal(TrimString(s))
}

function GetTokens(input: string, sep: string): seq<string>
  requires sep != ""
  ensures GetTokens(input, sep) == SplitString(input, sep)
{
  SplitString(input, sep)
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
  /* code modified by LLM (iteration 5): use ghost functions directly without compilation */
  var tokens := SplitString(input, sep);
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant tokens == SplitString(input, sep)
    invariant forall j :: 0 <= j < i ==> result[j] == StringToReal(TrimString(tokens[j]))
  {
    var value := StringToReal(TrimString(tokens[i]));
    result := result + [value];
    i := i + 1;
  }
}
// </vc-code>
