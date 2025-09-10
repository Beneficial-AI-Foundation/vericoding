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
lemma IntToStringLemma(n: int)
    ensures IntToString(n) == (if n == 0 then "" else IntToString(n / 10) + [('0' + (n % 10))])
{
}

lemma MaxCodersLemma(n: int)
    requires n >= 1
    ensures MaxCoders(n) == n * n / 2 + n * n % 2
{
}

function IntToString(n: int): string
{
    if n == 0 then "" else IntToString(n / 10) + [('0' + (n % 10))]
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<string>)
    requires ValidInput(n)
    ensures ValidOutputFormat(result, n)
    ensures ValidCheckerboardPlacement(result, n)
// </vc-spec>
// <vc-code>
{
    var max := MaxCoders(n);
    result := [IntToString(max)];
    var i := 1;
    while i <= n
        invariant |result| == i + 1
        invariant result[0] == IntToString(max)
        invariant forall k :: 1 <= k < i ==> |result[k]| == n
        invariant forall k :: 1 <= k < i ==> forall j :: 0 <= j < n ==>
            (result[k][j] == 'C' <==> 
                (if (k - 1) % 2 == 0 then j % 2 == 0 else j % 2 == 1))
    {
        var row: string := "";
        var j := 0;
        while j < n
            invariant |row| == j
            invariant forall k :: 0 <= k < j ==>
                (row[k] == 'C' <==> 
                    (if (i - 1) % 2 == 0 then k % 2 == 0 else k % 2 == 1))
        {
            if (i - 1) % 2 == 0 {
                if j % 2 == 0 {
                    row := row + ['C'];
                } else {
                    row := row + ['.'];
                }
            } else {
                if j % 2 == 1 {
                    row := row + ['C'];
                } else {
                    row := row + ['.'];
                }
            }
            j := j + 1;
        }
        result := result + [row];
        i := i + 1;
    }
}
// </vc-code>

