predicate ValidInput(n: int, k: int)
{
    n >= 1 && k >= 1
}

predicate AllRemaindersDistinct(n: int, k: int)
    requires ValidInput(n, k)
{
    forall i :: 1 <= i <= k ==> n % i == (i - 1)
}

predicate HasNonDistinctRemainder(n: int, k: int)
    requires ValidInput(n, k)
{
    exists i :: 1 <= i <= k && n % i != (i - 1)
}

// <vc-helpers>
lemma RemainderLemma(n: int, k: int, i: int)
    requires ValidInput(n, k)
    requires 1 <= i <= k
    ensures n % i == i - 1 <==> (n + 1) % i == 0
{
    // (n + 1) % i == 0 if and only if n % i == i - 1
    // This follows from the property: (a + b) % m = (a % m + b % m) % m
    // So (n + 1) % i = (n % i + 1) % i
    // If n % i == i - 1, then (i - 1 + 1) % i = i % i = 0
    // If (n + 1) % i == 0, then n % i must be i - 1
}

lemma LCMProperty(n: int, k: int)
    requires ValidInput(n, k)
    ensures AllRemaindersDistinct(n, k) <==> (forall i :: 1 <= i <= k ==> (n + 1) % i == 0)
{
}

function GCD(a: nat, b: nat): (result: nat)
    requires a > 0 || b > 0
    ensures result > 0
    ensures a % result == 0 && b % result == 0
    decreases a + b
{
    if b == 0 then
        a
    else
        GCD(b, a % b)
}

ghost function LCM(numbers: seq<nat>): nat
    requires |numbers| > 0
    requires forall i :: 0 <= i < |numbers| ==> numbers[i] > 0
    decreases numbers
{
    if |numbers| == 1 then
        numbers[0]
    else
        var a := numbers[0];
        var rest := numbers[1..];
        var lcm_rest := LCM(rest);
        (a * lcm_rest) / GCD(a, lcm_rest)
}

lemma LCMDivisible(lcm: nat, k: int)
    requires k >= 1
    requires lcm == LCM(SeqRange(1, k))
    ensures forall i :: 1 <= i <= k ==> lcm % i == 0
{
}

function SeqRange(start: nat, end: nat): seq<nat>
    requires start <= end
    ensures |SeqRange(start, end)| == end - start + 1
    ensures forall i :: 0 <= i < |SeqRange(start, end)| ==> SeqRange(start, end)[i] == start + i
{
    if start > end then
        []
    else
        [start] + SeqRange(start+1, end)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: string)
    requires ValidInput(n, k)
    ensures result == "Yes\n" <==> AllRemaindersDistinct(n, k)
    ensures result == "No\n" <==> HasNonDistinctRemainder(n, k)
// </vc-spec>
// <vc-code>
{
    if k == 1 {
        result := "Yes\n";
        return;
    }
    
    var lcm := 1;
    var i := 1;
    
    while i <= k
        invariant 1 <= i <= k + 1
        invariant lcm > 0
        invariant forall j :: 1 <= j < i ==> lcm % j == 0
    {
        if i > 1 {
            var gcd_val := GCD(lcm, i);
            lcm := lcm * i / gcd_val;
        }
        i := i + 1;
    }
    
    assert forall j :: 1 <= j <= k ==> lcm % j == 0;
    
    if (n + 1) % lcm == 0 {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>

