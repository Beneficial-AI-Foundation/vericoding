// <vc-preamble>
predicate ValidInput(n: int, k: int, a: array<int>, d: array<int>)
    reads a, d
{
    n >= 4 && 
    0 <= k < n &&
    a.Length == n && 
    d.Length == n &&
    (forall i :: 0 <= i < n ==> a[i] >= 1 && a[i] <= 1000000) &&
    (forall i :: 0 <= i < n ==> d[i] >= 1 && d[i] <= 1000000)
}

function SumArray(a: array<int>): int
    reads a
{
    SumArrayRange(a, 0, a.Length)
}

function SumArrayRange(a: array<int>, start: int, end: int): int
    requires 0 <= start <= end <= a.Length
    reads a
    decreases end - start
{
    if start >= end then 0
    else a[start] + SumArrayRange(a, start + 1, end)
}

function MinArrayRange(a: array<int>, start: int, end: int): int
    requires 0 <= start < end <= a.Length
    reads a
    decreases end - start
{
    if start == end - 1 then a[start]
    else
        var mid := (start + end) / 2;
        var leftMin := MinArrayRange(a, start, mid);
        var rightMin := MinArrayRange(a, mid, end);
        if leftMin <= rightMin then leftMin else rightMin
}
// </vc-preamble>

// <vc-helpers>
function TwoSmallestSum(a: array<int>): int
    requires a.Length >= 2
    reads a
{
    var min1 := MinArrayRange(a, 0, a.Length);
    var min2 := if a.Length == 2 then (if a[0] <= a[1] then a[1] else a[0])
                else SecondMinArray(a);
    min1 + min2
}

function SecondMinArray(a: array<int>): int
    requires a.Length >= 2
    reads a
{
    if a.Length == 2 then
        if a[0] <= a[1] then a[1] else a[0]
    else
        var min_val := MinArrayRange(a, 0, a.Length);
        SecondMinHelper(a, 0, min_val, 1000001)
}

function SecondMinHelper(a: array<int>, i: int, min_val: int, second_min: int): int
    requires 0 <= i <= a.Length
    requires a.Length >= 1
    reads a
    decreases a.Length - i
{
    if i >= a.Length then second_min
    else if a[i] > min_val && a[i] < second_min then
        SecondMinHelper(a, i + 1, min_val, a[i])
    else
        SecondMinHelper(a, i + 1, min_val, second_min)
}

function MaxOfFour(a: int, b: int, c: int, d: int): int
{
    var max_ab := if a >= b then a else b;
    var max_cd := if c >= d then c else d;
    if max_ab >= max_cd then max_ab else max_cd
}

function MaxChainValueFromPos(a: array<int>, d: array<int>, start_pos: int): int
    requires 0 <= start_pos < a.Length
    requires a.Length == d.Length
    reads a, d
{
    var curr := SumArrayRange(a, start_pos, a.Length);
    MaxChainHelper(a, d, start_pos, curr, 0)
}

function MaxChainHelper(a: array<int>, d: array<int>, pos: int, curr: int, best: int): int
    requires 0 <= pos <= a.Length
    requires a.Length == d.Length
    reads a, d
    decreases a.Length - pos
{
    if pos >= a.Length then best
    else
        var candidate := curr - d[pos];
        var newBest := if candidate > best then candidate else best;
        var newCurr := curr - a[pos];
        MaxChainHelper(a, d, pos + 1, newCurr, newBest)
}

function MaxChainValue(a: array<int>, d: array<int>, n: int): int
    requires n >= 1
    requires a.Length == n
    requires d.Length == n
    reads a, d
{
    MaxChainValueHelper(a, d, n, 0, SumArray(a), 0)
}

function MaxChainValueHelper(a: array<int>, d: array<int>, n: int, pos: int, curr: int, best: int): int
    requires n >= 1
    requires a.Length == n
    requires d.Length == n
    requires 0 <= pos <= n
    reads a, d
    decreases n - pos
{
    if pos >= n then best
    else
        var candidate := curr - d[pos];
        var newBest := if candidate > best then candidate else best;
        var newCurr := curr - a[pos];
        MaxChainValueHelper(a, d, n, pos + 1, newCurr, newBest)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: array<int>, d: array<int>) returns (result: int)
    requires ValidInput(n, k, a, d)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    if n == 1 {
        result := a[0] - d[0];
        return;
    }

    if k == 0 {
        // Simple chain case: find best excitation point
        var best := 0;
        var curr := SumArray(a);
        var i := 0;
        while i < n {
            var candidate := curr - d[i];
            if candidate > best {
                best := candidate;
            }
            curr := curr - a[i];
            i := i + 1;
        }
        result := best;
    } else if k == 1 {
        // One bond change case
        var best := SumArrayRange(a, 0, n - 1) - MinArrayRange(d, 0, n - 1);

        // Strategy: remove two smallest d values
        var sortedD := new int[n];
        var i := 0;
        while i < n {
            sortedD[i] := d[i];
            i := i + 1;
        }

        // Simple bubble sort for sortedD
        i := 0;
        while i < n {
            var j := 0;
            while j < n - 1 {
                if sortedD[j] > sortedD[j + 1] {
                    var temp := sortedD[j];
                    sortedD[j] := sortedD[j + 1];
                    sortedD[j + 1] := temp;
                }
                j := j + 1;
            }
            i := i + 1;
        }

        var other := SumArray(a) - sortedD[0] - sortedD[1];
        if other > best {
            best := other;
        }

        // Chain strategy starting from position i > 0
        var curr := SumArray(a);
        i := 0;
        while i < n {
            if i > 0 {
                var candidate := curr - d[i];
                if candidate > best {
                    best := candidate;
                }
            }
            curr := curr - a[i];
            i := i + 1;
        }

        // Strategy: excite first, remove smallest from rest
        if n >= 2 {
            var o2 := SumArray(a) - MinArrayRange(a, 1, n) - d[0];
            if o2 > best {
                best := o2;
            }
        }

        if best < 0 {
            best := 0;
        }
        result := best;
    } else {
        // k >= 2 case
        var option1 := SumArray(a) - MinArrayRange(d, 0, n - 1);
        var option2 := 0;
        var option3 := a[n - 1] - d[n - 1];

        result := option1;
        if option2 > result {
            result := option2;
        }
        if option3 > result {
            result := option3;
        }
    }
}
// </vc-code>
