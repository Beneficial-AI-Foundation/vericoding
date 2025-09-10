predicate ValidOutput(n: int, result: seq<string>)
    requires n >= 2
{
    if n < 6 then
        |result| == 1 + (n - 1) &&
        result[0] == "-1" &&
        (forall i :: 1 <= i < |result| ==> result[i] == "1 " + IntToString(i + 1))
    else
        |result| == (5 + (n - 6)) + (n - 1) &&
        result[0] == "1 2" && result[1] == "1 3" && result[2] == "1 4" && 
        result[3] == "2 5" && result[4] == "2 6" &&
        (forall i :: 5 <= i < 5 + (n - 6) ==> result[i] == "1 " + IntToString(i + 2)) &&
        (forall i :: 5 + (n - 6) <= i < |result| ==> result[i] == "1 " + IntToString(i - (5 + (n - 6)) + 2))
}

function IntToString(n: int): string
    decreases n < 0, if n >= 0 then n else -n
{
    if n < 0 then "-" + IntToString(-n)
    else if n < 10 then [n as char + '0']
    else IntToString(n / 10) + IntToString(n % 10)
}

// <vc-helpers>
function method IntToString(n: int): string
    decreases n < 0, if n >= 0 then n else -n
{
    if n < 0 then "-" + IntToString(-n)
    else if n < 10 then "" + n
    else IntToString(n / 10) + IntToString(n % 10)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<string>)
    requires n >= 2
    ensures ValidOutput(n, result)
// </vc-spec>
// <vc-code>
{
    if n < 6 {
        result := ["-1"];
        var i: int := 1;
        while i < n
            invariant 1 <= i <= n
            invariant |result| == i
            invariant result[0] == "-1"
            invariant forall j :: 1 <= j < i ==> result[j] == "1 " + IntToString(j + 1)
        {
            result := result + ["1 " + IntToString(i + 1)];
            i := i + 1;
        }
        return result;
    } else {
        result := ["1 2", "1 3", "1 4", "2 5", "2 6"];
        var i: int := 6;
        while i < n
            invariant 6 <= i <= n
            invariant result[0] == "1 2" && result[1] == "1 3" && result[2] == "1 4" && 
                     result[3] == "2 5" && result[4] == "2 6"
            invariant |result| == 5 + (i - 6)
            invariant forall j :: 5 <= j < |result| ==> result[j] == "1 " + IntToString(j + 2)
        {
            result := result + ["1 " + IntToString(i + 1)];
            i := i + 1;
        }

        var initial_len := |result|;
        var j: int := 1;
        while j < n
            invariant 1 <= j <= n
            invariant initial_len <= |result| <= initial_len + (j - 1)
            invariant result[0] == "1 2" && result[1] == "1 3" && result[2] == "1 4" && 
                     result[3] == "2 5" && result[4] == "2 6"
            invariant forall k :: 5 <= k < initial_len ==> result[k] == "1 " + IntToString(k + 2)
            invariant forall k :: initial_len <= k < |result| ==> result[k] == "1 " + IntToString(k - initial_len + 2)
        {
            if j == 1 { // skip "1 1"
                j := j + 1;
                continue;
            }
            result := result + ["1 " + IntToString(j + 1)];
            j := j + 1;
        }
        return result;
    }
}
// </vc-code>

