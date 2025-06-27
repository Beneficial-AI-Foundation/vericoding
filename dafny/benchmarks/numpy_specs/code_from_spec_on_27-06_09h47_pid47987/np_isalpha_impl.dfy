//https://numpy.org/doc/stable/reference/generated/numpy.char.isalpha.html#numpy.char.isalpha

//Returns true for each element if all characters in the data interpreted as a string are alphabetic and there is at least one character, false otherwise.
method isAlpha(input: array<string>) returns (ret: array<bool>)
    requires input != null
    ensures ret != null && ret.Length == input.Length
    ensures forall i :: 0 <= i < input.Length ==> ret[i] == (|input[i]| > 0 && forall j :: 0 <= j < |input[i]| ==> 'A' <= input[i][j] <= 'Z' || 'a' <= input[i][j] <= 'z')
{
    ret := new bool[input.Length];
    
    for i := 0 to input.Length
        invariant 0 <= i <= input.Length
        invariant forall k :: 0 <= k < i ==> ret[k] == (|input[k]| > 0 && forall j :: 0 <= j < |input[k]| ==> 'A' <= input[k][j] <= 'Z' || 'a' <= input[k][j] <= 'z')
    {
        if |input[i]| == 0 {
            ret[i] := false;
        } else {
            var allAlpha := true;
            for j := 0 to |input[i]|
                invariant 0 <= j <= |input[i]|
                invariant allAlpha == forall k :: 0 <= k < j ==> 'A' <= input[i][k] <= 'Z' || 'a' <= input[i][k] <= 'z'
            {
                if !('A' <= input[i][j] <= 'Z' || 'a' <= input[i][j] <= 'z') {
                    allAlpha := false;
                }
            }
            ret[i] := allAlpha;
        }
    }
}