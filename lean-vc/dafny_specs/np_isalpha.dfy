//https://numpy.org/doc/stable/reference/generated/numpy.char.isalpha.html#numpy.char.isalpha

//Returns true for each element if all characters in the data interpreted as a string are alphabetic and there is at least one character, false otherwise.
method isAlpha(input: array<string>) returns (ret: array<bool>)
    requires input != null
    ensures ret != null && ret.Length == input.Length
    ensures forall i :: 0 <= i < input.Length ==> ret[i] == (|input[i]| > 0 && forall j :: 0 <= j < |input[i]| ==> 'A' <= input[i][j] <= 'Z' || 'a' <= input[i][j] <= 'z')
{}