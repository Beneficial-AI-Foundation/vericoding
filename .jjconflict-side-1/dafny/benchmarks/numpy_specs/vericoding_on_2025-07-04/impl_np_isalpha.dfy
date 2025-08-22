//IMPL
method isAlpha(input: array<string>) returns (ret: array<bool>)
    requires input != null
    ensures ret != null && ret.Length == input.Length
    ensures forall i :: 0 <= i < input.Length ==> ret[i] == (|input[i]| > 0 && forall j :: 0 <= j < |input[i]| ==> 'A' <= input[i][j] <= 'Z' || 'a' <= input[i][j] <= 'z')
{
    ret := new bool[input.Length];
    
    var i := 0;
    while i < input.Length
        invariant 0 <= i <= input.Length
        invariant forall k :: 0 <= k < i ==> ret[k] == (|input[k]| > 0 && forall j :: 0 <= j < |input[k]| ==> 'A' <= input[k][j] <= 'Z' || 'a' <= input[k][j] <= 'z')
    {
        if |input[i]| == 0 {
            ret[i] := false;
        } else {
            var j := 0;
            var isAllAlpha := true;
            while j < |input[i]| && isAllAlpha
                invariant 0 <= j <= |input[i]|
                invariant isAllAlpha <==> forall k :: 0 <= k < j ==> 'A' <= input[i][k] <= 'Z' || 'a' <= input[i][k] <= 'z'
            {
                if !('A' <= input[i][j] <= 'Z' || 'a' <= input[i][j] <= 'z') {
                    isAllAlpha := false;
                }
                j := j + 1;
            }
            ret[i] := isAllAlpha;
        }
        i := i + 1;
    }
}