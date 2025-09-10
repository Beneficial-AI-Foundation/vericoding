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
lemma SequenceConstruction(n: int)
    requires n >= 2
{
}

function SeqFromTo(start: int, end: int): seq<string>
    requires start <= end
    ensures |SeqFromTo(start, end)| == end - start + 1
    ensures forall i :: 0 <= i < |SeqFromTo(start, end)| ==> SeqFromTo(start, end)[i] == "1 " + IntToString(start + i)
{
    if start == end then ["1 " + IntToString(start)]
    else ["1 " + IntToString(start)] + SeqFromTo(start + 1, end)
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
        var i := 2;
        while i <= n
            invariant 2 <= i <= n + 1
            invariant |result| == 1 + (i - 2)
            invariant result[0] == "-1"
            invariant forall j :: 1 <= j < |result| ==> result[j] == "1 " + IntToString(j + 1)
        {
            result := result + ["1 " + IntToString(i)];
            i := i + 1;
        }
    } else {
        result := ["1 2", "1 3", "1 4", "2 5", "2 6"];
        var i := 6;
        while i <= n
            invariant 6 <= i <= n + 1
            invariant |result| == 5 + (i - 6)
            invariant result[0] == "1 2" && result[1] == "1 3" && result[2] == "1 4" && result[3] == "2 5" && result[4] == "2 6"
            invariant forall j :: 5 <= j < |result| ==> result[j] == "1 " + IntToString(j + 1)
        {
            result := result + ["1 " + IntToString(i)];
            i := i + 1;
        }
        var k := 2;
        while k <= n
            invariant 2 <= k <= n + 1
            invariant |result| == 5 + (n - 6) + (k - 2)
            invariant result[0] == "1 2" && result[1] == "1 3" && result[2] == "1 4" && result[3] == "2 5" && result[4] == "2 6"
            invariant forall j :: 5 <= j < 5 + (n - 6) ==> result[j] == "1 " + IntToString(j + 1)
            invariant forall j :: 5 + (n - 6) <= j < |result| ==> result[j] == "1 " + IntToString(j - (5 + (n - 6)) + 2)
        {
            result := result + ["1 " + IntToString(k)];
            k := k + 1;
        }
    }
}
// </vc-code>

