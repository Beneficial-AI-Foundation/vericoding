Given an integer n (2 ≤ n ≤ 10^5), construct two trees with n nodes each:
1. First tree: Where Mahmoud's algorithm produces incorrect minimum vertex cover size
2. Second tree: Where Mahmoud's algorithm produces correct minimum vertex cover size
Mahmoud's algorithm roots the tree at node 1, counts nodes at even/odd depths,
and returns min(evenCnt, oddCnt) as the vertex cover size.

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

method solve(n: int) returns (result: seq<string>)
    requires n >= 2
    ensures ValidOutput(n, result)
{
    var first_tree: seq<string> := [];
    var second_tree: seq<string> := [];

    // First tree - where Mahmoud's algorithm is incorrect
    if n < 6 {
        first_tree := ["-1"];
    } else {
        var edges: seq<string> := [];
        edges := edges + ["1 2"];
        edges := edges + ["1 3"];  
        edges := edges + ["1 4"];
        edges := edges + ["2 5"];
        edges := edges + ["2 6"];

        assert |edges| == 5;
        assert edges[0] == "1 2" && edges[1] == "1 3" && edges[2] == "1 4";
        assert edges[3] == "2 5" && edges[4] == "2 6";

        var i := 7;
        while i <= n
            invariant 7 <= i <= n + 1
            invariant |edges| == 5 + (i - 7)
            invariant edges[0] == "1 2" && edges[1] == "1 3" && edges[2] == "1 4"
            invariant edges[3] == "2 5" && edges[4] == "2 6"
            invariant forall k :: 5 <= k < |edges| ==> edges[k] == "1 " + IntToString(k + 2)
        {
            var tmpCall1 := IntToString(i);
            edges := edges + ["1 " + tmpCall1];
            i := i + 1;
        }
        first_tree := edges;
        assert |first_tree| == 5 + (n - 6);
    }

    // Second tree - star graph where Mahmoud's algorithm is correct
    var star_edges: seq<string> := [];
    var j := 2;
    while j <= n
        invariant 2 <= j <= n + 1
        invariant |star_edges| == j - 2
        invariant forall k :: 0 <= k < |star_edges| ==> star_edges[k] == "1 " + IntToString(k + 2)
    {
        var tmpCall2 := IntToString(j);
        star_edges := star_edges + ["1 " + tmpCall2];
        j := j + 1;
    }
    second_tree := star_edges;
    assert |second_tree| == n - 1;

    result := first_tree + second_tree;
}
