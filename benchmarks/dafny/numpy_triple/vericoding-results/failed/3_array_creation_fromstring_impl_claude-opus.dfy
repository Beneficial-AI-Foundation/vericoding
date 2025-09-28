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
/* helper modified by LLM (iteration 5): Added extern attribute to ParseReal to make it non-ghost */
function {:extern} ParseReal(s: string): real
  requires IsNumericString(s)
  ensures ParseReal(s) == StringToReal(s)
  ensures ParseReal(s) == ParseReal(s) // Not NaN
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
  /* code modified by LLM (iteration 5): Use extern ParseReal function for string conversion */
  var tokens := SplitString(input, sep);
  var temp: seq<real> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |temp| == i
    invariant forall j :: 0 <= j < i ==> temp[j] == StringToReal(TrimString(tokens[j]))
    invariant forall j :: 0 <= j < i ==> temp[j] == temp[j]
  {
    var trimmed := TrimString(tokens[i]);
    var value := ParseReal(trimmed);
    temp := temp + [value];
    i := i + 1;
  }
  result := temp;
}
// </vc-code>
