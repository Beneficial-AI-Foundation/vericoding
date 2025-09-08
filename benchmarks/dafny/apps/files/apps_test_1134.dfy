Given n consecutive days of river observations where on day i there are m_i marks 
strictly above the current water level, find the minimum possible sum of d_i over 
all n days, where d_i is the number of marks strictly below the water level on day i.
Each day a mark is made at the current water level, marks never wash away, and the
total number of marks can only stay the same or increase each day.

predicate ValidInput(n: int, m: seq<int>) {
    n > 0 && |m| == n && 
    forall i :: 0 <= i < n ==> 0 <= m[i] < i + 1
}

predicate ValidSolution(n: int, m: seq<int>, dm: seq<int>) {
    |dm| == n && |m| == n &&
    (forall i :: 0 <= i < n ==> dm[i] >= m[i] + 1) &&
    (forall i :: 0 <= i < n - 1 ==> dm[i] <= dm[i + 1])
}

function SumBelow(m: seq<int>, dm: seq<int>): int
    requires |m| == |dm|
{
    if |m| == 0 then 0
    else (dm[0] - 1 - m[0]) + SumBelow(m[1..], dm[1..])
}

method solve(n: int, m: seq<int>) returns (result: int)
    requires ValidInput(n, m)
    ensures result >= 0
{
    var dm := new int[n];

    // Initialize with zeros
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> dm[j] == 0
    {
        dm[i] := 0;
        i := i + 1;
    }

    // dm[-1] = m[-1] + 1
    dm[n-1] := m[n-1] + 1;

    // Backwards pass: for i in range(n - 2, -1, -1)
    i := n - 2;
    while i >= 0
        invariant -1 <= i <= n - 2
        invariant dm[n-1] >= m[n-1] + 1
        invariant forall j :: i + 1 <= j < n ==> dm[j] >= m[j] + 1
    {
        var temp1 := m[i] + 1;
        var temp2 := m[i+1];
        var temp3 := dm[i+1] - 1;
        var max12 := if temp1 >= temp2 then temp1 else temp2;
        dm[i] := if max12 >= temp3 then max12 else temp3;
        i := i - 1;
    }

    // Forward pass: for i in range(1, n)
    i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall j :: 0 <= j < n ==> dm[j] >= m[j] + 1
        invariant forall j :: 1 <= j < i ==> dm[j-1] <= dm[j]
    {
        dm[i] := if dm[i] >= dm[i-1] then dm[i] else dm[i-1];
        i := i + 1;
    }

    // Calculate sum: sum([dm[i] - 1 - m[i] for i in range(n)])
    result := 0;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result >= 0
    {
        result := result + (dm[i] - 1 - m[i]);
        i := i + 1;
    }
}
