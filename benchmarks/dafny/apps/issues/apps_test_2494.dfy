// <vc-preamble>
predicate ValidInput(K: int) {
    K >= 2 && K <= 100000
}

function digitSum(n: int): int
    requires n > 0
    decreases n
{
    if n < 10 then n else (n % 10) + digitSum(n / 10)
}

predicate IsMultiple(n: int, K: int) 
    requires K > 0
{
    n > 0 && n % K == 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(K: int) returns (result: int)
    requires ValidInput(K)
    ensures result >= 1
// </vc-spec>
// <vc-code>
{
    var INF := 1000000000;
    var res := new int[K];

    var i := 0;
    while i < K
        invariant 0 <= i <= K
        invariant res.Length == K
        invariant forall j: int :: 0 <= j < i ==> res[j] == INF
    {
        res[i] := INF;
        i := i + 1;
    }

    res[1] := 1;

    var queueSize := K * 20;
    var queue := new int[queueSize];
    var front := queueSize / 2;
    var back := front;

    queue[back] := 1;
    back := back + 1;

    var iterations := 0;
    var maxIterations := K * K;

    while front < back && iterations < maxIterations
        invariant 0 <= front <= back <= queueSize
        invariant res.Length == K
        invariant queue.Length == queueSize
        invariant res[1] == 1
        invariant forall r: int :: 0 <= r < K ==> res[r] >= 1
        invariant forall j: int :: front <= j < back ==> 0 <= queue[j] < K
        decreases maxIterations - iterations
    {
        var r := queue[front];
        front := front + 1;
        iterations := iterations + 1;

        if r == 0 {
            break;
        }

        var nr0 := (10 * r) % K;
        if res[r] < res[nr0] {
            res[nr0] := res[r];
            if front > 0 {
                front := front - 1;
                queue[front] := nr0;
            }
        }

        var nr1 := (r + 1) % K;
        if res[r] + 1 < res[nr1] {
            res[nr1] := res[r] + 1;
            if back < queueSize {
                queue[back] := nr1;
                back := back + 1;
            }
        }
    }

    result := if res[0] == INF then 1 else res[0];

    if result < 1 {
        result := 1;
    }
}
// </vc-code>
