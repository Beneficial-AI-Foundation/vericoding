predicate ValidInput(n: int) {
    n >= 1
}

function MaxCoders(n: int): int
    requires n >= 1
{
    n * n / 2 + n * n % 2
}

predicate ValidOutputFormat(result: seq<string>, n: int) 
    requires n >= 1
{
    |result| == n + 1 &&
    result[0] == IntToString(MaxCoders(n)) &&
    (forall i :: 1 <= i <= n ==> |result[i]| == n)
}

predicate ValidCheckerboardPlacement(result: seq<string>, n: int)
    requires n >= 1
    requires ValidOutputFormat(result, n)
{
    forall i :: 1 <= i <= n ==> forall j :: 0 <= j < n ==>
        (result[i][j] == 'C' <==> 
            (if (i - 1) % 2 == 0 then j % 2 == 0 else j % 2 == 1))
}

// <vc-helpers>
//
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<string>)
    requires ValidInput(n)
    ensures ValidOutputFormat(result, n)
    ensures ValidCheckerboardPlacement(result, n)
// </vc-spec>
// <vc-code>
{
    var result: seq<string> := [IntToString(MaxCoders(n))];
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant |result| == i
        invariant result[0] == IntToString(MaxCoders(n))
        invariant forall k :: 1 <= k < i ==> |result[k]| == n
        invariant forall k :: 1 <= k < i ==> forall j :: 0 <= j < n ==>
            (result[k][j] == 'C' <==> if (k - 1) % 2 == 0 then j % 2 == 0 else j % 2 == 1)
    {
        var row: string := "";
        var j := 0;
        while j < n
            invariant 0 <= j <= n
            invariant |row| == j
            invariant forall l :: 0 <= l < j ==>
                (row[l] == 'C' <==> if (i - 1) % 2 == 0 then l % 2 == 0 else l % 2 == 1)
        {
            if (i - 1) % 2 == 0 {
                row := if j % 2 == 0 then row + "C" else row + " ";
            } else {
                row := if j % 2 == 1 then row + "C" else row + " ";
            }
            j := j + 1;
        }
        result := result + [row];
        i := i + 1;
    }
}
// </vc-code>

