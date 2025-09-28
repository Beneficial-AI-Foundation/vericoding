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
function AddDigitsWithCarry(d1: nat, d2: nat, carry: nat): (sum: nat, newCarry: nat)
    requires d1 < 10 && d2 < 10 && carry < 2
    ensures sum < 10 && newCarry < 2
    ensures d1 + d2 + carry == sum + 10 * newCarry
{
    var total := d1 + d2 + carry;
    if total < 10 then
        (total, 0)
    else
        (total - 10, 1)
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
{
    /* code modified by LLM (iteration 5): Fixed syntax errors in invariants and array slicing */
    var maxLen := if l1.Length > l2.Length then l1.Length else l2.Length;
    var resultArr := new nat[maxLen + 1];
    var carry := 0;
    var i := 0;
    
    while i < maxLen
        invariant 0 <= i <= maxLen
        invariant carry < 2
        invariant forall j :: 0 <= j < i ==> resultArr[j] < 10
        invariant ListToNat(resultArr[0..i]) + carry * (ListToNat([10]) * i) == ListToNat(l1[0..(if i < l1.Length then i else l1.Length)]) + ListToNat(l2[0..(if i < l2.Length then i else l2.Length)])
    {
        var d1 := if i < l1.Length then l1[i] else 0;
        var d2 := if i < l2.Length then l2[i] else 0;
        var res := AddDigitsWithCarry(d1, d2, carry);
        resultArr[i] := res.sum;
        carry := res.newCarry;
        i := i + 1;
    }
    
    if carry > 0 {
        resultArr[maxLen] := carry;
        result := resultArr[0..maxLen + 1];
    } else {
        result := resultArr[0..maxLen];
    }
}
// </vc-code>
