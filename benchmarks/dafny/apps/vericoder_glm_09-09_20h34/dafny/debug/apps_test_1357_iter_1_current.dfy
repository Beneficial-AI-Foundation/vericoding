predicate ValidInput(n: int, m: int, tasks: seq<int>)
{
    n >= 2 && m >= 1 && |tasks| == m && 
    forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
}

function MinTimeToComplete(n: int, tasks: seq<int>, currentPos: int, taskIndex: int): int
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires 1 <= currentPos <= n
    requires 0 <= taskIndex < |tasks|
{
    var target := tasks[taskIndex];
    if target >= currentPos then target - currentPos
    else (n - currentPos) + target
}

// <vc-helpers>
function MinTimeToCompleteAll(n: int, tasks: seq<int>): int
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires |tasks| > 0
{
    if |tasks| == 1 then MinTimeToComplete(n, tasks, 1, 0)
    else MinTimeToComplete(n, tasks, 1, 0) + MinTimeToCompleteAll(n, tasks[1:])
}

lemma MinTimeToCompleteAllBounds(n: int, m: int, tasks: seq<int>)
    requires ValidInput(n, m, tasks)
    requires m > 0
    ensures MinTimeToCompleteAll(n, tasks) >= tasks[m-1] - 1
    ensures MinTimeToCompleteAll(n, tasks) <= (m - 1) * n + tasks[m-1] - 1
{
    if m == 1 {
        calc {
            MinTimeToCompleteAll(n, tasks);
            MinTimeToComplete(n, tasks, 1, 0);
            { reveal MinTimeToComplete(); }
            if tasks[0] >= 1 then tasks[0] - 1 else (n - 1) + tasks[0];
        }
    } else {
        calc {
            MinTimeToCompleteAll(n, tasks);
            MinTimeToComplete(n, tasks, 1, 0) + MinTimeToCompleteAll(n, tasks[1:]);
            >= MinTimeToComplete(n, tasks, 1, 0) + (tasks[m-1] - 1);
        }
        calc {
            MinTimeToCompleteAll(n, tasks);
            MinTimeToComplete(n, tasks, 1, 0) + MinTimeToCompleteAll(n, tasks[1:]);
            <= MinTimeToComplete(n, tasks, 1, 0) + ((m - 2) * n + tasks[m-1] - 1);
            <= (n - 1) + ((m - 2) * n + tasks[m-1] - 1);
            == (m - 1) * n + tasks[m-1] - 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, tasks: seq<int>) returns (result: int)
    requires ValidInput(n, m, tasks)
    ensures result >= 0
    ensures m > 0 ==> result >= tasks[m-1] - 1
    ensures result <= (m - 1) * n + tasks[m-1] - 1
// </vc-spec>
// <vc-code>
{
    if m == 0 {
        result := 0;
    } else {
        result := MinTimeToCompleteAll(n, tasks);
        MinTimeToCompleteAllBounds(n, m, tasks);
    }
}
// </vc-code>

