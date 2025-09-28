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
/* helper modified by LLM (iteration 5): recursive ghost function to build expected result sequence from tokens */
ghost function BuildResults(tokens: seq<string>, n: nat): seq<real>
  requires |tokens| == n
  requires forall i :: 0 <= i < |tokens| ==> TrimString(tokens[i]) != ""
  requires forall i :: 0 <= i < |tokens| ==> IsNumericString(TrimString(tokens[i]))
  decreases n
  ensures |BuildResults(tokens, n)| == n
  ensures forall i :: 0 <= i < n ==> BuildResults(tokens, n)[i] == StringToReal(TrimString(tokens[i]))
{
  if n == 0 then
    []
  else
    BuildResults(tokens[..n-1], n-1) + [StringToReal(TrimString(tokens[n-1]))]
}

/* helper modified by LLM (iteration 5): lemma establishing existence of a result sequence satisfying the specification */
lemma ExistenceResult(input: string, sep: string, n: nat)
  requires sep != ""
  requires n > 0
  requires var tokens := SplitString(input, sep);
           |tokens| == n
  requires var tokens := SplitString(input, sep);
           |tokens| > 0 &&
           (forall i :: 0 <= i < |tokens| ==> TrimString(tokens[i]) != "") &&
           (forall i :: 0 <= i < |tokens| ==> IsNumericString(TrimString(tokens[i])))
  ensures exists res: seq<real> ::
            |res| == n && forall i :: 0 <= i < |res| ==> res[i] == StringToReal(TrimString(SplitString(input, sep)[i]))
{
  ghost var tokens := SplitString(input, sep);
  ghost var expected := BuildResults(tokens, n);
  assert |expected| == n;
  assert tokens == SplitString(input, sep);
  assert forall i :: 0 <= i < |expected| ==> expected[i] == StringToReal(TrimString(SplitString(input, sep)[i]));
  assert exists res: seq<real> :: res == expected && |res| == n && (forall i :: 0 <= i < |res| ==> res[i] == StringToReal(TrimString(SplitString(input, sep)[i])));
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
  /* code modified by LLM (iteration 5): choose result via such-that using only spec-level functions; existence justified by lemma */
  ExistenceResult(input, sep, n);
  result :| |result| == n &&
            (forall i :: 0 <= i < |result| ==> result[i] == StringToReal(TrimString(SplitString(input, sep)[i])));
}

// </vc-code>
