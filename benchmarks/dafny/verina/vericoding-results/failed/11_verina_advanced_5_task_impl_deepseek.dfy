// <vc-preamble>
function ListToNat(l: seq<nat>): nat
    decreases |l|
{
    if |l| == 0 then
        0
    else
        l[0] + 10 * ListToNat(l[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove problematic NatToList and keep only necessary helpers for array operations */
function Max(a: int, b: int): int { if a > b then a else b }

lemma ListToNatDistributive(l1: seq<nat>, l2: seq<nat>)
    ensures ListToNat(l1 + l2) == ListToNat(l1) + ListToNat(l2) * (if |l1| == 0 then 1 else 10)
    decreases |l1|
{
    if |l1| > 0 {
        ListToNatDistributive(l1[1..], l2);
    }
}
// </vc-helpers>

// <vc-spec>
method AddTwoNumbers(l1: array<nat>, l2: array<nat>) returns (result: array<nat>)
    requires 
        l1.Length > 0 &&
        l2.Length > 0 &&
        (forall i :: 0 <= i < l1.Length ==> l1[i] < 10) &&
        (forall i :: 0 <= i < l2.Length ==> l2[i] < 10) &&
        (l1[l1.Length - 1] != 0 || (l1.Length == 1 && l1[0] == 0)) &&
        (l2[l2.Length - 1] != 0 || (l2.Length == 1 && l2[0] == 0))
    ensures
        result.Length > 0 &&
        ListToNat(result[..]) == ListToNat(l1[..]) + ListToNat(l2[..]) &&
        (forall i :: 0 <= i < result.Length ==> result[i] < 10) &&
        (result[result.Length - 1] != 0 || (l1.Length == 1 && l1[0] == 0 && l2.Length == 1 && l2[0] == 0 && result.Length == 1 && result[0] == 0))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix array assignment by converting sequence to array properly */
{
    var maxLength := Max(l1.Length, l2.Length);
    var tempResult := new nat[maxLength + 1];
    var carry := 0;
    var i := 0;
    
    while i < maxLength
        invariant 0 <= i <= maxLength
        invariant carry >= 0 && carry < 10
        invariant forall j :: 0 <= j < i ==> tempResult[j] < 10
        decreases maxLength - i
    {
        var digit1 := if i < l1.Length then l1[i] else 0;
        var digit2 := if i < l2.Length then l2[i] else 0;
        var sum := digit1 + digit2 + carry;
        tempResult[i] := sum % 10;
        carry := sum / 10;
        i := i + 1;
    }
    
    var resultLength := if carry > 0 then maxLength + 1 else maxLength;
    result := new nat[resultLength];
    
    var j := 0;
    while j < resultLength
        invariant 0 <= j <= resultLength
        invariant forall k :: 0 <= k < j ==> result[k] == tempResult[k]
        decreases resultLength - j
    {
        result[j] := tempResult[j];
        j := j + 1;
    }
}
// </vc-code>
