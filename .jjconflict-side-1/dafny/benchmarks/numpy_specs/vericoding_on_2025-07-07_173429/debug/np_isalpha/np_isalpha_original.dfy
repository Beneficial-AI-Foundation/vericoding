//SPEC
method isAlpha(input: array<string>) returns (ret: array<bool>)
    requires input != null
    ensures ret != null && ret.Length == input.Length
    ensures forall i :: 0 <= i < input.Length ==> ret[i] == (|input[i]| > 0 && forall j :: 0 <= j < |input[i]| ==> 'A' <= input[i][j] <= 'Z' || 'a' <= input[i][j] <= 'z')
{}