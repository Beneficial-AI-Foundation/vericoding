// <vc-preamble>
predicate ValidInput(N: int) {
    N >= 1 && N <= 100000
}

predicate ValidResult(N: int, result: int) {
    result >= 1 && 
    result <= N + 1 &&
    (exists i :: 0 <= i <= N && result == digitSum6(i) + digitSum9(N - i)) &&
    (forall i :: 0 <= i <= N ==> result <= digitSum6(i) + digitSum9(N - i))
}
// </vc-preamble>

// <vc-helpers>
function digitSum6(n: int): int
    requires n >= 0
    ensures digitSum6(n) >= 1
    ensures digitSum6(n) <= n + 1
    decreases n
{
    if n == 0 then 1 else (n % 6) + digitSum6(n / 6)
}

function digitSum9(n: int): int
    requires n >= 0  
    ensures digitSum9(n) >= 0
    ensures digitSum9(n) <= n
    decreases n
{
    if n == 0 then 0 else (n % 9) + digitSum9(n / 9)
}
// </vc-helpers>

// <vc-spec>
method solve(N: int) returns (result: int)
    requires ValidInput(N)
    ensures ValidResult(N, result)
// </vc-spec>
// <vc-code>
{
    var res := digitSum6(0) + digitSum9(N);
    var i := 0;
    var witnessI := 0;

    while i <= N
        invariant 0 <= i <= N + 1
        invariant 0 <= witnessI <= N
        invariant N - witnessI >= 0
        invariant res == digitSum6(witnessI) + digitSum9(N - witnessI)
        invariant forall j :: 0 <= j < i ==> res <= digitSum6(j) + digitSum9(N - j)
        invariant res >= 1
        invariant res <= N + 1
    {
        var cc := digitSum6(i) + digitSum9(N - i);

        if res > cc {
            res := cc;
            witnessI := i;
        }

        i := i + 1;
    }

    result := res;
}
// </vc-code>
